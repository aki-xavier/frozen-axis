"""Component-level measurement of Criterion P4 on the probe's task.

Criterion P4 has three components; this script measures each on the constructed
task of experiments/probe.py and reports the risk-gap floor they imply,

    kappa = p * delta^2 / 16 - rho,

together with the risk gap actually realized by the frozen families on the same
task, so that the bound and the measurement can be compared directly.

Definitions used here (all in the units of the field, not of the weights):

  ambiguity family   pairs of fields that are indistinguishable from the
                     evidence, because they differ only inside the observation
                     hole.  The perturbation moves the fine-scale ridge of the
                     field by one position while it lies inside the hole.
  delta              separation of the two demanded reconstructions, measured as
                     the largest per-position change over the hole; by
                     construction the evidence distance of the pair is zero.
  p                  realized mass: the fraction of hole positions at which the
                     demanded reconstruction moves by at least delta, averaged
                     over the test instances (a probability under the test
                     distribution, not a worst case).
  Lambda             bounded-description rate: the largest ratio of the change
                     in a rule's output on the hole to the change in the
                     observed evidence that produced it, over the frozen
                     families and over random evidence perturbations.
  rho                benchmark risk: the risk of the best evidence-instantiated
                     rule available on the same task (the SURE rule), measured
                     against the demanded reconstruction.

Run:  uv run --with numpy python experiments/p4_components.py
"""
import json
import os

import numpy as np

import probe as P

N, HOLE = P.N, P.HOLE


def field_ridge_inside(p_centre, w, ridge_rel):
    """Field whose fine-scale ridge sits ridge_rel positions inside the hole."""
    return P.bump(p_centre, w) + 0.3 * P.bump(p_centre + 14 + ridge_rel, 2.5)


def make_pair(p_centre, w, h0, shift=1):
    """Instance and its fine-scale perturbation, sharing one observation."""
    xa = field_ridge_inside(p_centre, w, 0)
    xb = field_ridge_inside(p_centre, w, shift)
    mask = np.ones(N, bool)
    mask[h0:h0 + HOLE] = False
    return xa, xb, mask


def demanded_reconstruction(x, mask):
    """The demand: the reconstruction the task itself would choose, computed
    with the true field known (the per-position oracle profile of the probe)."""
    hidden = np.where(mask, x, np.nan)          # noise-free evidence, cleanest demand
    filled = np.interp(np.arange(N), np.where(mask)[0], x[mask])
    R = P.oracle_profile(x, hidden, mask)
    return P.reconstruct(hidden, mask, R)


def measure(n_inst=24, seed=11):
    rng = np.random.default_rng(seed)
    deltas, masses, rho_terms, gaps = [], [], [], []

    # frozen families from the probe's own training run
    train = P.build("id", P.N_TRAIN, 20260921)
    lam_off = P.offline_scalar(train)
    table = P.offline_table(train, lam_off)
    frozen = [("frozen scalar", np.full(N, lam_off)), ("frozen table", table)]

    for _ in range(n_inst):
        p_centre = int(rng.integers(14, N - 30))
        w = float(rng.uniform(4.0, 8.0))
        h0 = int(rng.integers(p_centre + 10, p_centre + 16))   # ridge inside the hole
        xa, xb, mask = make_pair(p_centre, w, h0)
        ta, tb = demanded_reconstruction(xa, mask), demanded_reconstruction(xb, mask)
        sep = np.abs(ta - tb)
        # the evidence is identical for the pair, so any separation is at scale zero
        delta = float(np.max(sep))
        if delta <= 1e-9:
            continue
        deltas.append(delta)
        masses.append(float(np.mean(sep >= delta)))

        sigma = P.SIGMA
        hidden = np.where(mask, xa, np.nan)
        filled = np.interp(np.arange(N), np.where(mask)[0], xa[mask])
        obs = np.where(mask, xa + rng.normal(0.0, sigma, N), np.nan)
        hid = np.where(mask, obs, np.nan)
        fil = np.interp(np.arange(N), np.where(mask)[0], obs[mask])

        # rho: risk of the best evidence-instantiated rule on this instance
        lam_sure = P.sure_scalar(hid, mask, fil)
        r_sure = P.reconstruct(hid, mask, np.full(N, lam_sure))
        rho_terms.append(float(np.mean((r_sure - ta) ** 2)))
        for _, R in frozen:
            r_frozen = P.reconstruct(hid, mask, R)
            gaps.append(float(np.mean((r_frozen - ta) ** 2) - np.mean((r_sure - ta) ** 2)))

    # Lambda: response of the frozen maps to an evidence perturbation
    lam_rates = []
    for _, R in frozen:
        for _ in range(n_inst):
            p_centre = int(rng.integers(14, N - 30))
            w = float(rng.uniform(4.0, 8.0))
            h0 = int(rng.integers(p_centre + 10, p_centre + 16))
            x = field_ridge_inside(p_centre, w, 0)
            mask = np.ones(N, bool)
            mask[h0:h0 + HOLE] = False
            e = rng.normal(0.0, P.SIGMA, N)
            e[~mask] = 0.0
            f0 = np.where(mask, x, np.nan)
            f1 = np.where(mask, x + e, np.nan)
            f0 = np.nan_to_num(f0, nan=0.0)
            f1 = np.nan_to_num(f1, nan=0.0)
            if np.linalg.norm(e) < 1e-12:
                continue
            d_out = P.reconstruct(f1, mask, R) - P.reconstruct(f0, mask, R)
            lam_rates.append(float(np.linalg.norm(d_out) / np.linalg.norm(e)))

    delta = float(np.median(deltas))
    p = float(np.mean(masses))
    rho = float(np.mean(rho_terms))
    lam = float(np.max(lam_rates))
    kappa = p * delta ** 2 / 16.0 - rho
    out = {
        "n_pairs": len(deltas),
        "delta_median": delta, "delta_max": float(np.max(deltas)),
        "p_realized": p,
        "Lambda_max": lam,
        "rho_benchmark": rho,
        "kappa_floor": kappa,
        "gap_measured_frozen": float(np.mean(gaps)),
        "gap_min_frozen": float(np.min(gaps)),
    }
    return out


if __name__ == "__main__":
    res = measure()
    print(json.dumps(res, indent=1))
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "p4_components.json"), "w") as fh:
        json.dump(res, fh, indent=1)
    print("written to experiments/p4_components.json")
