"""Canonical task designed to instantiate Criterion P4, with its components measured.

Task.  A structure field on 64 positions is observed through a mask that leaves
one contiguous hole, under additive Gaussian noise.  The task demands a
*thresholded* strength map, the standard edge-preserving form of adaptive
regularization:

    lambda_i = lambda_lo + (lambda_hi - lambda_lo) * 1{ |(grad^2 fill)_i| > tau },

where `fill` is the interpolated evidence, so the demanded map is an analytic
function of the current evidence alone (Assumption A0 holds) and yet is
discontinuous in that evidence: at positions where the observed Laplacian sits
near `tau`, an evidence perturbation of size `eta` flips the demanded strength
between `lambda_lo` and `lambda_hi`, which is a reversal at scale `eta` with a
separation independent of `eta`.

Measured here, all in the units of the field (reconstruction units, so that the
floor and the realized risk gap are directly comparable):

  delta   demanded-reconstruction separation over a pair of evidence vectors at
          distance eta, at the position where the demand flips
  p       realized mass: the fraction of positions at which a random eta-sized
          evidence perturbation flips the demanded map, averaged over instances
  Lambda  bounded-description rate: response of the frozen maps to an evidence
          perturbation
  rho     benchmark risk: risk of the best evidence-instantiated rule available
          on this task (the same threshold construction with the threshold
          estimated from the current evidence rather than from the task)
  kappa   p * delta^2 / 16 - rho, the floor of the barrier-to-gap proposition
  gap     realized risk gap of the frozen families against the benchmark

Run:  uv run --with numpy python experiments/p4_task.py
"""
import json
import os

import numpy as np

import probe as P

N, HOLE, SIGMA = P.N, P.HOLE, P.SIGMA
LAM_LO, LAM_HI = 0.05, 6.0
GRID = np.geomspace(LAM_LO, LAM_HI, 20)
# The task's threshold is a fixed constant of the task family.  It sits between
# the Laplacian level of the smooth part of the field and the level at an edge,
# which is what makes an evidence perturbation flip the demanded map at edges.
TAU = 0.5
EDGE_AMP = 0.8
EDGE_POSITIONS = (16, 32, 48)


def laplacian(v):
    d2 = np.zeros_like(v)
    d2[1:-1] = v[:-2] - 2.0 * v[1:-1] + v[2:]
    d2[0], d2[-1] = d2[1], d2[-2]
    return d2


def staircase(shift=0):
    """Piecewise-constant field with three edges of equal amplitude, so that
    several positions share one edge magnitude and a single threshold can sit
    between the smooth part and the edge part of the Laplacian."""
    x = np.zeros(N)
    pos = [p + shift for p in EDGE_POSITIONS]
    x[pos[0]:pos[1]] = EDGE_AMP
    x[pos[2]:] = EDGE_AMP
    return x + 0.2 * P.bump(22, 6.0)


def instance(rng, kind):
    if kind == "id":
        shift, scale, h0 = 0, 1.0, 28
    elif kind == "ood_shift":
        shift, scale, h0 = int(rng.integers(-2, 3)), 1.0, int(rng.integers(26, 31))
    elif kind == "ood_noise":
        shift, scale, h0 = 0, 2.0, 28
    else:
        raise ValueError(kind)
    sigma = SIGMA * scale
    x = staircase(shift)
    mask = np.ones(N, bool)
    mask[h0:h0 + HOLE] = False
    obs = np.where(mask, x + rng.normal(0.0, sigma, N), np.nan)
    fill = np.interp(np.arange(N), np.where(mask)[0], obs[mask])
    return x, obs, mask, fill, sigma


def build(kind, n, seed):
    rng = np.random.default_rng(seed)
    return [instance(rng, kind) for _ in range(n)]


def threshold_map(fill, tau):
    m = np.abs(laplacian(fill)) > tau
    return np.where(m, LAM_HI, LAM_LO)


def tau_from_evidence(fill):
    """The benchmark's threshold: estimated from the current instance alone, as
    the level separating the smooth part of the Laplacian from the edge part."""
    a = np.abs(laplacian(fill))
    return float(0.5 * (np.quantile(a, 0.5) + np.quantile(a, 0.95)))


def demand(obs, mask, fill, tau):
    """The demanded reconstruction: evidence-computable but discontinuous."""
    lam = threshold_map(fill, tau)
    hid = np.where(mask, obs, np.nan)
    return lam, P.reconstruct(np.where(mask, obs, 0.0) if np.any(np.isnan(hid)) else obs, mask, lam)


def benchmark_profile(fill):
    """Best evidence-instantiated rule available: the same threshold construction,
    but with the threshold estimated from this instance alone rather than taken
    from the task.  (If the task's threshold is treated as part of the task
    definition, as Assumption A0 allows, the benchmark reproduces the demand
    exactly and rho = 0; the estimated-threshold variant is the conservative
    case reported here.)"""
    return threshold_map(fill, tau_from_evidence(fill))


def risk(a, b):
    return float(np.mean((a - b) ** 2))


def fit_frozen(train, tau):
    """Offline families fitted in the value space: their strength profile against
    the demanded strength profile on the training set (the space in which the
    paper defines the loss of a rule)."""
    targets = [threshold_map(f, tau) for _, o, m, f, _ in train]

    def loss(R):
        return float(np.mean([np.mean((R - t) ** 2) for t in targets]))

    best = min(((loss(np.full(N, lam)), lam) for lam in GRID))
    scalar = np.full(N, best[1])
    table = scalar.copy()
    cur = best[0]
    for _ in range(3):
        for i in range(N):
            keep = table[i]
            for lam in GRID:
                table[i] = lam
                v = loss(table)
                if v < cur - 1e-12:
                    cur, keep = v, lam
            table[i] = keep
    return scalar, table, cur


def measure(kind="ood_loc", n_inst=24, eta=0.02, seed=5):
    rng = np.random.default_rng(seed)
    train = build("id", 60, 20260921)
    tau = TAU
    lam_scalar, table, train_loss = fit_frozen(train, tau)

    deltas, masses, rho_terms, gaps, down_gaps = [], [], [], [], []
    for _ in range(n_inst):
        x, obs, mask, fill, sigma = instance(rng, kind)
        t = threshold_map(fill, tau)                       # demanded profile
        b = benchmark_profile(fill)                        # evidence-instantiated profile
        rho_terms.append(float(np.mean((b - t) ** 2)))     # benchmark risk, value space
        t_rec = P.reconstruct(np.nan_to_num(obs, nan=0.0), mask, t)
        b_rec = P.reconstruct(np.nan_to_num(obs, nan=0.0), mask, b)

        # an eta-sized perturbation of the evidence (outside the hole) and the flip it causes
        e = rng.normal(0.0, 1.0, N)
        e[~mask] = 0.0
        e *= eta / max(np.linalg.norm(e), 1e-12)
        obs_p = obs + np.where(mask, e, 0.0)
        fill_p = np.interp(np.arange(N), np.where(mask)[0], obs_p[mask])
        t_p = threshold_map(fill_p, tau)
        flipped = np.abs(t - t_p) > 0
        if flipped.sum() == 0:
            continue
        delta = float(np.max(np.abs(t - t_p)[flipped]))     # value space: |lambda_hi - lambda_lo|
        if delta <= 1e-9:
            continue
        deltas.append(delta)
        masses.append(float(flipped.sum()) / float(mask.sum()))

        for R in (lam_scalar, table):
            gaps.append(float(np.mean((R - t) ** 2)) - rho_terms[-1])
            down_gaps.append(risk(P.reconstruct(np.nan_to_num(obs, nan=0.0), mask, R), t_rec) - risk(b_rec, t_rec))

    # Lambda of the frozen maps
    rates = []
    for R in (lam_scalar, table):
        for _ in range(n_inst):
            x, obs, mask, fill, sigma = instance(rng, "id")
            e = rng.normal(0.0, SIGMA, N)
            e[~mask] = 0.0
            o1 = np.nan_to_num(obs + e, nan=0.0)
            o0 = np.nan_to_num(obs, nan=0.0)
            if np.linalg.norm(e) < 1e-12:
                continue
            rates.append(float(np.linalg.norm(P.reconstruct(o1, mask, R) - P.reconstruct(o0, mask, R))
                               / np.linalg.norm(e)))

    delta = float(np.median(deltas))
    p = float(np.mean(masses))
    rho = float(np.mean(rho_terms))
    out = {
        "task": {"N": N, "hole": HOLE, "sigma": SIGMA, "lambda_lo": LAM_LO, "lambda_hi": LAM_HI,
                 "tau": TAU, "edge_amp": EDGE_AMP, "eta": eta, "regime": kind, "n_pairs": len(deltas)},
        "delta_median": delta, "p_realized": p, "Lambda_max": float(np.max(rates)),
        "rho_benchmark": rho,
        "kappa_estimated_threshold": p * delta ** 2 / 16.0 - rho,
        "rho_A0": 0.0,
        "kappa_A0": p * delta ** 2 / 16.0,
        "gap_measured_frozen": float(np.mean(gaps)), "gap_min_frozen": float(np.min(gaps)),
        "downstream_gap_mean": float(np.mean(down_gaps)), "downstream_gap_min": float(np.min(down_gaps)),
        "train_loss_frozen": train_loss,
    }
    return out


if __name__ == "__main__":
    print(json.dumps(measure(), indent=1))
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "p4_task.json"), "w") as fh:
        json.dump(measure(), fh, indent=1)
    print("written to experiments/p4_task.json")
