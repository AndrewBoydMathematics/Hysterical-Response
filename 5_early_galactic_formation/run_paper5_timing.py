"""Paper 5 timing-viability experiments (former Paper 5.1 suite).

Integrates the post-recombination dust system in e-fold time N = ln a:
  δ'' + (2 + dlnH/dN) δ' = (3/2) Ω_clust(a) (δ + x)
  x' = κ δ - g x
with x ≡ β q. Reports nonlinear-crossing redshifts, loss/activation scans,
seed dependence, and amplification histories. Generates PDF figures for TeX.
"""
from __future__ import annotations

import json
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

HERE = Path(__file__).resolve().parent

H0 = 67.4
Om0 = 0.315
Ob0h2 = 0.0224
h = H0 / 100.0
Ob0 = Ob0h2 / h**2
Or0 = 9.2e-5
OL0 = 1.0 - Om0 - Or0


def E(a: float) -> float:
    return float(np.sqrt(Or0 * a ** (-4) + Om0 * a ** (-3) + OL0))


def dlnH_dN(a: float) -> float:
    num = -4.0 * Or0 * a ** (-5) - 3.0 * Om0 * a ** (-4)
    return (a / (2.0 * E(a) ** 2)) * num


def Omega_frac(a: float, Omega0: float) -> float:
    return Omega0 * a ** (-3) / E(a) ** 2


def rhs(N: float, y, kappa: float, g: float, Omega0_clust: float):
    delta, ddelta, x = y
    a = float(np.exp(N))
    coeff = 2.0 + dlnH_dN(a)
    d2 = -coeff * ddelta + 1.5 * Omega_frac(a, Omega0_clust) * (delta + x)
    dx = kappa * delta - g * x
    return [ddelta, d2, dx]


def integrate(
    kappa: float,
    g: float = 0.0,
    z_on: float = 1089.0,
    delta_i: float = 1e-5,
    z_min: float = 0.0,
    Omega0_clust: float = Ob0,
    response: bool = True,
):
    a_i = 1.0 / (1.0 + z_on)
    N_i = float(np.log(a_i))
    N_f = float(np.log(1.0 / (1.0 + z_min)))
    y0 = [delta_i, 0.0, 0.0 if response else 0.0]
    k_eff = kappa if response else 0.0

    def event(N, y):
        return y[0] - 1.0

    event.terminal = True
    event.direction = 1

    Ns = np.linspace(N_i, N_f, 2500)
    sol = solve_ivp(
        lambda N, y: rhs(N, y, k_eff, g if response else 0.0, Omega0_clust),
        (N_i, N_f),
        y0,
        t_eval=Ns,
        rtol=1e-7,
        atol=1e-9,
        events=event,
    )
    z = 1.0 / np.exp(sol.t) - 1.0
    delta = sol.y[0]
    x = sol.y[2]
    znl = float("nan")
    if sol.t_events and sol.t_events[0].size:
        znl = float(1.0 / np.exp(sol.t_events[0][0]) - 1.0)
    elif delta[-1] >= 1.0:
        # crossed between samples
        idx = np.where(delta >= 1.0)[0]
        if idx.size:
            znl = float(z[idx[0]])
    return z, delta, x, znl


def z_nl(kappa: float, g: float = 0.0, z_on: float = 1089.0, delta_i: float = 1e-5) -> float:
    return integrate(kappa, g=g, z_on=z_on, delta_i=delta_i)[3]


def kappa_crit(
    z_target: float = 14.0,
    g: float = 0.0,
    z_on: float = 1089.0,
    k_lo: float = 50.0,
    k_hi: float = 1200.0,
) -> float:
    def f(k: float) -> float:
        z = z_nl(k, g=g, z_on=z_on)
        return (z - z_target) if np.isfinite(z) else -1e3

    hi = k_hi
    flo, fhi = f(k_lo), f(hi)
    while flo * fhi > 0 and hi < 5000:
        hi *= 1.5
        fhi = f(hi)
    return float(brentq(f, k_lo, hi))


def style_axes(ax):
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlim(1e3, 1)
    ax.set_xlabel("redshift $z$")
    ax.grid(True, which="both", alpha=0.25)


def fig_growth():
    fig, ax = plt.subplots(figsize=(6.2, 4.0))
    # baryons only
    z, d, _, _ = integrate(0.0, response=False, Omega0_clust=Ob0)
    ax.plot(z, np.clip(d, 1e-6, None), "k--", lw=1.2, label="baryons only")
    # total matter clustering, no response
    z, d, _, _ = integrate(0.0, response=False, Omega0_clust=Om0)
    ax.plot(z, np.clip(d, 1e-6, None), "k:", lw=1.2, label="standard total-matter")
    for k, c in [(100, "#1f77b4"), (130, "#d62728"), (150, "#2ca02c")]:
        z, d, _, znl = integrate(k, g=0.0)
        ax.plot(z, np.clip(d, 1e-6, None), color=c, lw=1.6, label=rf"Hysterical $\kappa={k}$")
    ax.axhline(1.0, color="0.4", lw=0.8)
    ax.axvline(14.32, color="0.5", lw=0.8, ls="-.")
    ax.text(14.32 * 1.05, 2.5e-5, "JADES-GS-z14-0", rotation=90, fontsize=8, color="0.35", va="bottom")
    style_axes(ax)
    ax.set_ylim(1e-5, 3)
    ax.set_ylabel(r"matter contrast $\delta$")
    ax.set_title("Post-recombination perturbation growth")
    ax.legend(fontsize=8, loc="upper left")
    fig.tight_layout()
    fig.savefig(HERE / "paper5_growth_histories.pdf")
    plt.close(fig)


def fig_activation():
    fig, ax = plt.subplots(figsize=(6.2, 4.0))
    zons = np.array([1089, 900, 800, 700, 600, 500, 400, 300, 250, 200])
    for g, ls in [(0.0, "-"), (0.3, "--"), (1.0, "-."), (3.0, ":")]:
        ks = [kappa_crit(14.0, g=g, z_on=float(z)) for z in zons]
        ax.plot(zons, ks, ls=ls, lw=1.6, label=rf"$g=\gamma/H={g:g}$")
    ax.set_xlabel(r"activation redshift $z_{\mathrm{on}}$")
    ax.set_ylabel(r"minimum $\kappa=\beta\sigma/H$ for $\delta=1$ by $z=14$")
    ax.set_title("Cost of delaying the Hysterical instability")
    ax.set_xlim(1100, 180)
    ax.set_yscale("log")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(fontsize=8)
    fig.tight_layout()
    fig.savefig(HERE / "paper5_activation_cost.pdf")
    plt.close(fig)


def fig_amplification():
    fig, ax = plt.subplots(figsize=(6.2, 4.0))
    z, d, x, _ = integrate(130.0, g=0.0)
    ax.plot(z, np.clip(d, 1e-6, None), lw=1.6, label=r"$\delta$")
    ax.plot(z, np.clip(x, 1e-6, None), lw=1.6, label=r"$x=\beta q$")
    ax.axhline(1.0, color="0.4", lw=0.8)
    style_axes(ax)
    ax.set_ylim(1e-5, 3e2)
    ax.set_ylabel("perturbation amplitude")
    ax.set_title(r"Hysterical-field amplification ($\kappa=130$, $g=0$)")
    ax.legend(fontsize=9)
    fig.tight_layout()
    fig.savefig(HERE / "paper5_amplification.pdf")
    plt.close(fig)


def fig_seeds():
    fig, ax = plt.subplots(figsize=(6.2, 4.0))
    seeds = np.array([1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8])
    znls = [z_nl(150.0, g=0.0, delta_i=float(s)) for s in seeds]
    ax.plot(seeds, znls, "o-", lw=1.5)
    ax.set_xscale("log")
    ax.set_xlabel(r"initial seed $\delta_i$")
    ax.set_ylabel(r"nonlinear-crossing redshift $z_{\mathrm{nl}}$")
    ax.set_title(r"Smaller seeds collapse later ($\kappa=150$, $g=0$)")
    ax.grid(True, which="both", alpha=0.25)
    fig.tight_layout()
    fig.savefig(HERE / "paper5_seed_dependence.pdf")
    plt.close(fig)


def main() -> None:
    table_g0 = {str(k): z_nl(k) for k in [50, 80, 100, 130, 150, 200, 300, 500]}
    loss_table = {str(g): kappa_crit(14.0, g=g) for g in [0.0, 0.3, 1.0, 3.0]}
    delayed = {
        str(z_on): kappa_crit(14.0, g=0.0, z_on=z_on)
        for z_on in [1089, 600, 400, 300, 200]
    }
    seeds = {
        f"{di:.0e}": z_nl(150.0, delta_i=di)
        for di in [1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8]
    }

    out = {
        "background": {
            "H0": H0,
            "Om0": Om0,
            "Ob0h2": Ob0h2,
            "Ob0": Ob0,
            "Or0": Or0,
            "OL0": OL0,
        },
        "znl_vs_kappa_g0": table_g0,
        "kappa_crit_znl14_vs_g": loss_table,
        "kappa_crit_znl14_vs_zon_g0": delayed,
        "znl_vs_seed_kappa150_g0": seeds,
        "kappa_crit_znl14_g0": kappa_crit(14.0, g=0.0),
    }
    (HERE / "paper5_timing_viability.json").write_text(
        json.dumps(out, indent=2), encoding="utf-8"
    )
    fig_growth()
    fig_activation()
    fig_amplification()
    fig_seeds()
    print(json.dumps(out, indent=2))
    print("Wrote figures:", list(HERE.glob("paper5_*.pdf")))


if __name__ == "__main__":
    main()
