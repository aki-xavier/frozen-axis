"""Minimal empirical probe for the open inversion task of the paper.

Task.  A structure field x on 64 positions (a smooth bump and a narrow ridge)
is observed through a mask that leaves one contiguous hole, under additive
Gaussian noise, so the task is ill-posed (P1) and the evidence does not
determine the field on the hole.  For each instance the strength the task
requires is the per-position profile of the quadratic smoother
    sum_i m_i (obs_i - d_i)^2 + sum_i R_i (d_i - d_{i+1})^2
that minimises the reconstruction error; the experimenter computes that profile
offline and no rule may see it.

Rules compared.
  frozen scalar        one lambda selected offline on the training distribution
                       (Mode B; classical offline parameter selection)
  frozen table         one lambda per position selected offline on the training
                       distribution (Mode B; the frozen parameter table, 64
                       numbers fixed before inference begins)
  amortized net        ridge map from evidence features to the whole strength
                       profile, fitted on the training distribution (Mode B by
                       source: its weights are corpus statistics)
  SURE scalar (Mode A) lambda chosen per instance from the current evidence by
                       Stein's unbiased risk estimate, with the noise scale
                       estimated from the same instance (no training data)
  oracle scalar        per-instance lambda chosen with the true field known
  oracle profile       per-position profile chosen with the true field known
                       (the floor; the demanded strength itself)

Reported per regime: mean reconstruction RMSE, excess over the per-position
oracle, and the gap to the best evidence-instantiated rule available.

Honest scope.  One constructed task, one finite frozen family, one noise model.
The probe measures the risk gap of Section 5.4 on this task; it is not a test of
Criterion P4 on real data, and the barrier condition is not exercised here.

Run:  uv run --with numpy --with matplotlib python experiments/probe.py
"""
import json
import os

import numpy as np

N, HOLE, SIGMA = 64, 12, 0.25
LAM_GRID = np.geomspace(0.02, 30.0, 12)
TRAIN_BUMP = (22, 6.0)               # bump centre and width seen in training


def smooth(v, k):
    return np.convolve(v, np.ones(k) / k, mode="same") if k > 1 else v.copy()


def bump(p, w):
    return np.exp(-0.5 * ((np.arange(N) - p) / w) ** 2)


def field(p, w):
    return bump(p, w) + 0.3 * bump(p + 14, 2.5)


def instance(rng, kind):
    if kind == "id":
        p, w, scale = TRAIN_BUMP[0], TRAIN_BUMP[1], 1.0
    elif kind == "ood_loc":
        p, w, scale = int(rng.integers(8, N - 8)), TRAIN_BUMP[1], 1.0
    elif kind == "ood_width":
        p, w, scale = TRAIN_BUMP[0], float(rng.uniform(1.5, 3.0)), 1.0
    elif kind == "ood_noise":
        p, w, scale = TRAIN_BUMP[0], TRAIN_BUMP[1], 2.0
    else:
        raise ValueError(kind)
    sigma = SIGMA * scale
    x = field(p, w)
    obs = x + rng.normal(0.0, sigma, N)
    mask = np.ones(N, bool)
    h0 = int(rng.integers(2, N - HOLE - 2))
    mask[h0:h0 + HOLE] = False
    hidden = np.where(mask, obs, np.nan)
    filled = np.interp(np.arange(N), np.where(mask)[0], obs[mask])
    return x, hidden, mask, filled, sigma


def build(kind, n, seed):
    rng = np.random.default_rng(seed)
    return [instance(rng, kind) for _ in range(n)]


# ------------------------------------------------------------ solver --------
def solve_tri(diag, off, rhs):
    """Thomas algorithm; off[i] couples positions i and i+1."""
    b = diag.astype(float).copy()
    c = np.concatenate([off, [0.0]])
    d = rhs.astype(float).copy()
    for i in range(1, N):
        m = off[i - 1] / b[i - 1]
        b[i] -= m * c[i - 1]
        d[i] -= m * d[i - 1]
    x = np.zeros(N)
    x[-1] = d[-1] / b[-1]
    for i in range(N - 2, -1, -1):
        x[i] = (d[i] - c[i] * x[i + 1]) / b[i]
    return x


def system(mask, R):
    lam = 0.5 * (R[:-1] + R[1:])
    diag = np.where(mask, 1.0, 0.0).astype(float).copy()
    diag[:-1] += lam
    diag[1:] += lam
    return diag, -lam


def reconstruct(hidden, mask, R):
    diag, off = system(mask, R)
    return solve_tri(diag, off, np.where(mask, hidden, 0.0))


def inv_diag(diag, off):
    """Diagonal of the inverse of a symmetric tridiagonal matrix (Usmani)."""
    th = np.zeros(N + 1)
    th[0], th[1] = 1.0, diag[0]
    for i in range(2, N + 1):
        th[i] = diag[i - 1] * th[i - 1] - off[i - 2] ** 2 * th[i - 2]
    ph = np.zeros(N + 2)
    ph[N + 1], ph[N] = 1.0, diag[N - 1]
    for i in range(N - 1, 0, -1):
        ph[i] = diag[i - 1] * ph[i + 1] - off[i - 1] ** 2 * ph[i + 2]
    return np.array([th[i - 1] * ph[i + 1] / th[N] for i in range(1, N + 1)])


def rmse(x, hidden, mask, R):
    return float(np.sqrt(np.mean((reconstruct(hidden, mask, R) - x) ** 2)))


# ----------------------------------------------- evidence-based criteria ----
def sigma_hat(f):
    """Robust noise scale of the current instance: median|x_{i+1}-2x_i+x_{i-1}|
    divided by 0.6745*sqrt(6) is median-unbiased for iid Gaussian noise."""
    d2 = np.abs(np.diff(f, n=2))
    return float(np.median(d2) / (0.6745 * np.sqrt(6.0)))


def sure(hidden, mask, R, sigma):
    """Stein's unbiased risk estimate, up to the constant -m sigma^2."""
    diag, off = system(mask, R)
    d = solve_tri(diag, off, np.where(mask, hidden, 0.0))
    rss = float(np.sum((hidden[mask] - d[mask]) ** 2))
    df = float(np.sum(inv_diag(diag, off) * mask))
    return rss + 2.0 * sigma ** 2 * df


def sure_scalar(hidden, mask, f):
    """Mode A: the strength is instantiated from the current evidence alone."""
    sigma = max(sigma_hat(f), 1e-6)
    scores = [sure(hidden, mask, np.full(N, lam), sigma) for lam in LAM_GRID]
    return float(LAM_GRID[int(np.argmin(scores))])


def oracle_scalar(x, hidden, mask):
    errs = [np.mean((reconstruct(hidden, mask, np.full(N, lam)) - x) ** 2) for lam in LAM_GRID]
    return float(LAM_GRID[int(np.argmin(errs))])


def oracle_profile(x, hidden, mask, sweeps=3):
    R = np.full(N, LAM_GRID[0])
    best = float(np.mean((reconstruct(hidden, mask, R) - x) ** 2))
    for _ in range(sweeps):
        for i in range(N):
            keep = R[i]
            for lam in LAM_GRID:
                R[i] = lam
                v = float(np.mean((reconstruct(hidden, mask, R) - x) ** 2))
                if v < best - 1e-12:
                    best, keep = v, lam
            R[i] = keep
    return R


# ------------------------------------------------------- offline rules ------
def offline_scalar(train):
    best, out = np.inf, LAM_GRID[0]
    for lam in LAM_GRID:
        e = float(np.mean([rmse(x, h, m, np.full(N, lam)) for x, h, m, f, s in train]))
        if e < best:
            best, out = e, lam
    return float(out)


def offline_table(train, start, sweeps=3):
    R = np.full(N, start)
    cur = float(np.mean([rmse(x, h, m, R) for x, h, m, f, s in train]))
    for _ in range(sweeps):
        for i in range(N):
            keep = R[i]
            for lam in LAM_GRID:
                R[i] = lam
                e = float(np.mean([rmse(x, h, m, R) for x, h, m, f, s in train]))
                if e < cur - 1e-12:
                    cur, keep = e, lam
            R[i] = keep
    return R


def features(f):
    d2 = np.abs(np.diff(f, n=2))
    nl = smooth(np.concatenate([[d2[0]], d2, [d2[-1]]]), 9) / np.sqrt(6.0)
    cols = [nl] + [np.abs(np.diff(smooth(f, k), prepend=f[0])) for k in (3, 5, 9)]
    F = np.column_stack(cols)
    return np.column_stack([F] + [F[:, i] * F[:, j]
                                  for i in range(F.shape[1]) for j in range(i, F.shape[1])])


def fit_amortized(train, nfeat=8):
    T = np.array([oracle_profile(*d[:3]) for d in train])
    H = np.array([features(d[3]) for d in train])
    idx = list(range(min(nfeat, H.shape[2])))
    X = np.column_stack([np.ones(H.shape[0] * N), H[:, :, idx].reshape(-1, len(idx))])
    coef = np.linalg.solve(X.T @ X + 1e-8 * np.eye(X.shape[1]), X.T @ T.ravel())

    def rule(hidden, mask, f, _s=None):
        h = features(f)[:, idx]
        return np.clip(np.column_stack([np.ones(N), h]) @ coef, LAM_GRID[0], LAM_GRID[-1])
    return rule


REGIMES = ("id", "ood_loc", "ood_width", "ood_noise")
N_TRAIN, N_TEST = 120, 40


def main():
    train = build("id", N_TRAIN, 20260921)
    lam_off = offline_scalar(train)
    table = offline_table(train, lam_off)
    amort = fit_amortized(train[:60])

    rules = [("frozen scalar", lambda h, m, f, s: np.full(N, lam_off)),
             ("frozen table", lambda h, m, f, s: table.copy()),
             ("amortized net", lambda h, m, f, s: amort(h, m, f)),
             ("SURE scalar (Mode A)", lambda h, m, f, s: np.full(N, sure_scalar(h, m, f)))]

    print(f"offline scalar lambda* = {lam_off:.3f}; frozen table in "
          f"[{table.min():.3f}, {table.max():.3f}] with mean {table.mean():.3f}")
    results = {"lam_off": lam_off, "table": table.tolist(), "regimes": {}}
    for kind in REGIMES:
        D = build(kind, N_TEST, 7 if kind != "id" else 99)
        floor = np.array([rmse(d[0], d[1], d[2], oracle_profile(*d[:3])) for d in D])
        per = {}
        for name, fn in rules:
            errs = np.array([rmse(d[0], d[1], d[2], fn(d[1], d[2], d[3], d[4])) for d in D])
            lams = np.array([float(np.mean(fn(d[1], d[2], d[3], d[4]))) for d in D])
            per[name] = {"rmse": float(errs.mean()), "excess": float((errs - floor).mean()),
                         "lambda": float(lams.mean())}
        best_mode_a = per["SURE scalar (Mode A)"]["rmse"]
        for name in per:
            per[name]["gap_to_best_mode_a"] = per[name]["rmse"] - best_mode_a
        per["oracle profile (floor)"] = {"rmse": float(floor.mean()), "excess": 0.0,
                                        "lambda": float("nan"),
                                        "gap_to_best_mode_a": float(floor.mean() - best_mode_a)}
        osc = np.array([rmse(d[0], d[1], d[2], np.full(N, oracle_scalar(d[0], d[1], d[2])))
                        for d in D])
        olam = np.array([oracle_scalar(d[0], d[1], d[2]) for d in D])
        per["oracle scalar (reference)"] = {
            "rmse": float(osc.mean()), "excess": float((osc - floor).mean()),
            "lambda": float(olam.mean()),
            "gap_to_best_mode_a": float(osc.mean() - best_mode_a)}
        results["regimes"][kind] = per
        print(f"\n{kind}   (best Mode A rule: {best_mode_a:.4f})")
        print(f"  {'rule':24s} {'rmse':>8s} {'excess':>8s} {'gap':>8s} {'lambda':>8s}")
        for name, _ in rules + [("oracle scalar (reference)", None),
                                ("oracle profile (floor)", None)]:
            v = per[name]
            lam = "-" if np.isnan(v["lambda"]) else format(v["lambda"], ".3f")
            print(f"  {name:24s} {v['rmse']:8.4f} {v['excess']:8.4f} "
                  f"{v['gap_to_best_mode_a']:8.4f} {lam:>8s}")

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "probe_results.json"), "w") as fh:
        json.dump(results, fh, indent=1)
    try:
        import figure
        figure.plot(results, os.path.join(here, os.pardir, "figures"))
        print("\nfigure written to figures/probe.pdf")
    except ImportError as exc:            # numpy-only runs still work
        print(f"\n(matplotlib not available: {exc})")
    return results


if __name__ == "__main__":
    main()
