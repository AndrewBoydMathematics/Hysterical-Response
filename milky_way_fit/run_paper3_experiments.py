#!/usr/bin/env python3
"""Recompute Paper 3 Milky Way response experiments (no raw Gaia download).

Uses:
  - Adopted McMillan-type baryonic disc/bulge parameters (paper Table)
  - Feng et al. (2026) published Cepheid RC Table 1 (arxiv:2512.21780)
  - Söding et al. (2025) published local density constraint
  - Analytic response / RAR mappings from Papers 1–2 application
"""
from __future__ import annotations

import csv
import json
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

OUT = Path(__file__).resolve().parent

# ---------------------------------------------------------------------------
# Constants (astronomical)
# ---------------------------------------------------------------------------
G_PC = 4.3009172706e-3  # pc / Msun * (km/s)^2
KPC_TO_PC = 1e3
A0_M_S2 = 1.20e-10
MSUN_KG = 1.98847e30
G_SI = 6.67430e-11

R0_KPC = 8.2
A0 = A0_M_S2  # m/s^2


def VQ_from_BTFR(Mb_msun: float, a0: float = A0) -> float:
    """V_Q [km/s] from V_Q^4 = G a0 M_b."""
    M_kg = Mb_msun * MSUN_KG
    V4 = G_SI * a0 * M_kg  # (m/s)^4
    return (V4 ** 0.25) / 1000.0


def T_d(x: float) -> float:
    """Exponential enclosed-production transition: 1 - (1+x) e^{-x}."""
    return 1.0 - (1.0 + x) * np.exp(-x)


def disc_mass_stellar(Sigma0, Rd_kpc, z_d_kpc=None) -> float:
    """Total mass of exponential sech-like stellar disc: M = 2π Σ0 Rd^2."""
    return 2.0 * np.pi * Sigma0 * (Rd_kpc * KPC_TO_PC) ** 2


def disc_mass_gas(Sigma0, Rd_kpc, Rm_kpc) -> float:
    """Approximate gas disc mass ∫ 2π R Σ(R) dR with Σ∝exp(-Rm/R - R/Rd).

    Normalized so central midplane column matches McMillan-style Σ0 factor
    used in the TeX (ρ_g formula integrates vertically to Σ(R)).
    Vertical integral of (Σ0/(4 zd)) sech^2(z/(2zd)) is Σ0/2 * something:
    ∫ sech^2(z/(2zd)) dz = 2 zd, so ρ0=Σ0/(4 zd) → Σ_surface = Σ0/2.
    Use Σ(R)=(Σ0/2) exp(-Rm/R - R/Rd) as in McMillan HI/H2 forms.
    """
    R = np.linspace(1e-4, 60.0, 20000)  # kpc
    Sigma = 0.5 * Sigma0 * np.exp(-Rm_kpc / R - R / Rd_kpc)  # Msun/pc^2
    # convert: Σ in Msun/pc^2, R in kpc → mass = ∫ 2π (R*1000 pc) Σ d(R*1000)
    return float(np.trapezoid(2 * np.pi * (R * KPC_TO_PC) * Sigma * KPC_TO_PC, R))


def bulge_mass(rho0_b, r0=0.075, rcut=2.1, q=0.5) -> float:
    """Numerical mass of McMillan-like bulge density."""
    # Sample in cylindrical (R,z); r'^2 = R^2+(z/q)^2
    R = np.linspace(0.0, 8.0, 800)
    z = np.linspace(-6.0, 6.0, 800)
    RR, ZZ = np.meshgrid(R, z, indexing="ij")
    rp = np.sqrt(RR**2 + (ZZ / q) ** 2)
    rho = rho0_b / (1.0 + rp / r0) ** 1.8 * np.exp(-((rp / rcut) ** 2))
    # axisymmetric volume element 2π R dR dz; R,z in kpc → pc^3
    dR = R[1] - R[0]
    dz = z[1] - z[0]
    # only R>=0 grid already; mass = ∫ rho * 2π R dR dz with unit conversion
    mass = np.sum(rho * 2 * np.pi * RR) * dR * dz * (KPC_TO_PC**3)
    return float(mass)


def baryonic_Vc_approx(components, bulge_M, R_kpc: np.ndarray) -> np.ndarray:
    """Crude baryonic circular speed from enclosed sphericalized mass.

    Physical input / diagnostic only — not a full Poisson disc solve.
    """
    Menc = np.zeros_like(R_kpc, dtype=float)
    # Bulge: fully use erf-like enclosed via numerical shells
    rmax = 8.0
    r_grid = np.linspace(1e-4, rmax, 2000)
    # Approximate bulge enclosed with sphericalized r
    # Use cumulative of density on spherical r with q-correction ignored → order-of-magnitude
    # Prefer: treat bulge mass as Plummer-ish enclosed M_b * r^3/(r^2+a^2)^{1.5} with a=0.5 kpc
    a = 0.5
    Menc += bulge_M * R_kpc**3 / (R_kpc**2 + a**2) ** 1.5

    for M, Rd in components:
        x = R_kpc / Rd
        # Exponential disc enclosed (thin): M(<R)=M[1-(1+R/Rd)e^{-R/Rd}]
        Menc += M * T_d(x)

    # V^2 = G M/r with r in pc
    r_pc = R_kpc * KPC_TO_PC
    return np.sqrt(np.maximum(G_PC * Menc / r_pc, 0.0))


def rar_g(g_b: np.ndarray, a0_kms2_kpc: float) -> np.ndarray:
    """Empirical RAR interpolation g = g_b / (1 - exp(-sqrt(g_b/a0)))."""
    x = np.sqrt(np.maximum(g_b / a0_kms2_kpc, 0.0))
    return g_b / (1.0 - np.exp(-x))


def main() -> None:
    # --- Adopted disc parameters (paper Table) ---
    thin = dict(name="thin", Sigma0=896.0, Rd=2.50, zd=0.30)
    thick = dict(name="thick", Sigma0=183.0, Rd=3.02, zd=0.90)
    hi = dict(name="HI", Sigma0=53.1, Rd=7.0, zd=0.085, Rm=4.0)
    h2 = dict(name="H2", Sigma0=2180.0, Rd=1.5, zd=0.045, Rm=12.0)

    M_thin = disc_mass_stellar(thin["Sigma0"], thin["Rd"])
    M_thick = disc_mass_stellar(thick["Sigma0"], thick["Rd"])
    M_hi = disc_mass_gas(hi["Sigma0"], hi["Rd"], hi["Rm"])
    M_h2 = disc_mass_gas(h2["Sigma0"], h2["Rd"], h2["Rm"])

    # Choose bulge central density so total Mb ≈ 6.65e10 (paper adopted).
    # McMillan 2017 has Mb ~ few x 10^10; we calibrate rho0_b to hit target.
    Mb_target = 6.65e10
    M_discs = M_thin + M_thick + M_hi + M_h2
    M_bulge_needed = Mb_target - M_discs
    # Find rho0_b by scaling from a reference integration
    M_ref = bulge_mass(1.0)
    rho0_b = M_bulge_needed / M_ref if M_ref > 0 else 0.0
    M_bulge = bulge_mass(rho0_b)
    Mb = M_discs + M_bulge

    print("=== Baryonic masses [Msun] ===")
    for n, m in [
        ("thin", M_thin),
        ("thick", M_thick),
        ("HI", M_hi),
        ("H2", M_h2),
        ("bulge", M_bulge),
        ("TOTAL", Mb),
    ]:
        print(f"  {n:8s} {m:.4e}")

    VQ = VQ_from_BTFR(Mb)
    print(f"\nBTFR V_Q = {VQ:.4f} km/s  (a0={A0:.2e} m/s^2)")

    # Multi-component response production: weight by component mass, exponential discs.
    # Bulge treated as centrally concentrated → fully enclosed for R> few kpc (T=1).
    weights = [
        (M_thin, thin["Rd"]),
        (M_thick, thick["Rd"]),
        (M_hi, hi["Rd"]),
        (M_h2, h2["Rd"]),
        (M_bulge, None),  # point-like / fully enclosed
    ]
    Wtot = sum(w for w, _ in weights)

    def T_multi(R):
        acc = 0.0
        for W, Rd in weights:
            if Rd is None:
                acc += W / Wtot * 1.0
            else:
                acc += W / Wtot * T_d(R / Rd)
        return acc

    T_R0 = T_multi(R0_KPC)
    V_resp_R0 = VQ * np.sqrt(T_R0)

    # Baryonic V_b from sphericalized enclosed-mass diagnostic
    comps = [(M_thin, thin["Rd"]), (M_thick, thick["Rd"]), (M_hi, hi["Rd"]), (M_h2, h2["Rd"])]
    Vb_R0 = float(baryonic_Vc_approx(comps, M_bulge, np.array([R0_KPC]))[0])
    # Paper adopts Vb(R0)=176.5 from a full potential realization.
    # Prefer that literature-style input when our sphericalized estimate differs.
    Vb_adopted = 176.5
    Vc_R0 = float(np.sqrt(Vb_adopted**2 + V_resp_R0**2))

    print(f"T(R0) multi-component = {T_R0:.6f}")
    print(f"V_resp(R0) = {V_resp_R0:.4f} km/s")
    print(f"V_b(R0) sphericalized diagnostic = {Vb_R0:.4f} km/s")
    print(f"V_b(R0) adopted = {Vb_adopted:.4f} km/s")
    print(f"V_c(R0) prediction = {Vc_R0:.4f} km/s")
    print(f"Feng Vc(R0)=236.8 +/- 0.8;  delta = {Vc_R0 - 236.8:.4f} km/s")

    # Solar-normalized VQ from measured Vc
    Vc_obs = 236.8
    V_resp_sol = np.sqrt(max(Vc_obs**2 - Vb_adopted**2, 0.0))
    VQ_sol = V_resp_sol / np.sqrt(T_R0)
    a0_eff = (VQ_sol * 1000) ** 4 / (G_SI * Mb * MSUN_KG)
    print(f"Solar-norm VQ = {VQ_sol:.4f} km/s; a0_eff = {a0_eff:.3e} m/s^2")
    print(f"V_resp from Solar Vc = {V_resp_sol:.4f} km/s")

    # Analytic q_th from thin-disc Rd=2.5 (Paper 2 corollary)
    Rd_q = 2.5
    q_th = (1.0 + 6.0 * (Rd_q / R0_KPC) ** 2) ** (-0.5)
    print(f"\nq_th(R0) = {q_th:.6f}")

    # Vertical density mapping (fixed radial response at Solar-normalized V_resp)
    def rho_eff(q, Vresp=V_resp_sol):
        # ρ = V^2 / (4π G q^2 R0^2) with R0 in pc, V in km/s, G in pc/Msun (km/s)^2
        R0_pc = R0_KPC * KPC_TO_PC
        return Vresp**2 / (4 * np.pi * G_PC * q**2 * R0_pc**2)

    rho_gaia = 0.0117
    sigma_gaia = 0.0035
    rho_th = rho_eff(q_th)
    q_fit = float(np.sqrt(V_resp_sol**2 / (4 * np.pi * G_PC * rho_gaia * (R0_KPC * KPC_TO_PC) ** 2)))
    offset_sigma = (rho_th - rho_gaia) / sigma_gaia
    # 1σ density → q interval (rho ∝ 1/q^2)
    rho_lo, rho_hi = rho_gaia - sigma_gaia, rho_gaia + sigma_gaia
    q_hi = float(np.sqrt(V_resp_sol**2 / (4 * np.pi * G_PC * rho_lo * (R0_KPC * KPC_TO_PC) ** 2)))
    q_lo = float(np.sqrt(V_resp_sol**2 / (4 * np.pi * G_PC * rho_hi * (R0_KPC * KPC_TO_PC) ** 2)))
    print(f"rho_eff(q_th) = {rho_th:.6f} Msun/pc^3  ({offset_sigma:.3f} σ from Gaia)")
    print(f"q_fit = {q_fit:.6f};  1σ q interval ({q_lo:.4f}, {q_hi:.4f})")

    # Feng Table 1 (published; not a raw Gaia re-reduction)
    feng = np.array(
        [
            [6.58, 242.92, 1.25],
            [7.49, 239.31, 1.33],
            [8.48, 236.54, 0.86],
            [9.50, 232.36, 1.32],
            [10.52, 229.97, 1.13],
            [11.42, 233.57, 1.39],
            [12.50, 233.38, 1.30],
            [13.50, 237.05, 1.53],
            [14.46, 237.11, 1.31],
            [15.21, 237.00, 2.22],
            [15.88, 231.03, 1.95],
            [17.58, 224.03, 1.91],
        ]
    )
    R_obs, V_obs, s_obs = feng.T

    R_grid = np.linspace(5.0, 30.0, 400)
    T_grid = np.array([T_multi(R) for R in R_grid])
    Vb_grid = baryonic_Vc_approx(comps, M_bulge, R_grid)
    # Rescale baryonic curve to adopted Vb(R0) so radial shape is diagnostic
    Vb_grid = Vb_grid * (Vb_adopted / Vb_grid[np.argmin(np.abs(R_grid - R0_KPC))])

    V_resp_btfr = VQ * np.sqrt(T_grid)
    V_resp_sol_c = VQ_sol * np.sqrt(T_grid)
    Vc_btfr = np.sqrt(Vb_grid**2 + V_resp_btfr**2)
    Vc_sol = np.sqrt(Vb_grid**2 + V_resp_sol_c**2)

    # RAR on same baryonic acceleration
    # g_b = Vb^2/R with R in kpc → convert a0 to (km/s)^2 / kpc
    # a0 = 1.2e-10 m/s^2; 1 kpc = 3.085677581e19 m
    # a0_kms2_kpc = a0 * (1e-3 km/m)^2 / (1/kpc in 1/m) wait:
    # g [ (km/s)^2 / kpc ] = a0[m/s^2] * (1 km/1000 m)^2 / (1 kpc / 3.085677581e19 m)
    # = a0 * 1e-6 * 3.085677581e19 = a0 * 3.085677581e13
    a0_gal = A0 * 3.085677581e13  # (km/s)^2 / kpc
    g_b = Vb_grid**2 / R_grid
    g_rar = rar_g(g_b, a0_gal)
    Vc_rar = np.sqrt(g_rar * R_grid)

    g_resp_extra_sol = V_resp_sol_c**2 / R_grid
    g_rar_extra = g_rar - g_b
    ratio = g_resp_extra_sol / np.maximum(g_rar_extra, 1e-12)

    def metrics(Vc_model):
        V_m = np.interp(R_obs, R_grid, Vc_model)
        resid = V_m - V_obs
        chi2 = float(np.sum((resid / s_obs) ** 2))
        rms = float(np.sqrt(np.mean(resid**2)))
        return chi2, rms, V_m

    chi_btfr, rms_btfr, Vm_btfr = metrics(Vc_btfr)
    chi_sol, rms_sol, Vm_sol = metrics(Vc_sol)
    chi_rar, rms_rar, Vm_rar = metrics(Vc_rar)

    print("\n=== Feng 12-bin diagnostics ===")
    print(f"BTFR:  chi2={chi_btfr:.2f}, RMS={rms_btfr:.3f}")
    print(f"Solar: chi2={chi_sol:.2f}, RMS={rms_sol:.3f}")
    print(f"RAR:   chi2={chi_rar:.2f}, RMS={rms_rar:.3f}")
    for Rmark in [5.0, R0_KPC, 30.0]:
        print(f"resp/RAR extra @ {Rmark:.1f} kpc = {np.interp(Rmark, R_grid, ratio):.3f}")

    # ---- Figures ----
    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    ax.errorbar(R_obs, V_obs, yerr=s_obs, fmt="o", color="k", ms=5, label="Feng et al. Cepheid RC")
    ax.plot(R_grid, Vc_btfr, color="C0", lw=2.0, label="Response (BTFR norm.)")
    ax.plot(R_grid, Vc_sol, color="C0", lw=1.6, ls="--", label="Response (Solar norm.)")
    ax.plot(R_grid, Vc_rar, color="C3", lw=1.6, label="MOND/RAR (same baryons)")
    ax.plot(R_grid, Vb_grid, color="0.5", lw=1.2, ls=":", label="Baryons only")
    ax.axvline(R0_KPC, color="0.7", ls=":")
    ax.set_xlim(5.5, 18.5)
    ax.set_ylim(180, 270)
    ax.set_xlabel(r"$R$ [kpc]")
    ax.set_ylabel(r"$V_c$ [km s$^{-1}$]")
    ax.legend(frameon=False, fontsize=9)
    ax.set_title("Direct radial comparison (published Cepheid bins)")
    fig.tight_layout()
    fig.savefig(OUT / "paper3_gaia_radial_direct_test.png", dpi=160)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(7.2, 4.4))
    ax.plot(R_grid, ratio, color="C0", lw=2)
    ax.axhline(1.0, color="0.5", ls="--")
    ax.axvline(R0_KPC, color="0.7", ls=":")
    ax.set_xlim(5, 30)
    ax.set_xlabel(r"$R$ [kpc]")
    ax.set_ylabel(r"$g_{\mathrm{resp,extra}}/g_{\mathrm{RAR,extra}}$")
    ax.set_title("Response vs RAR extra-acceleration ratio (Solar-normalized)")
    fig.tight_layout()
    fig.savefig(OUT / "paper3_response_vs_rar_extra_ratio.png", dpi=160)
    plt.close(fig)

    # Vertical visualization
    z = np.linspace(0, 1.2, 200)  # kpc
    def Kz(q, Vresp=V_resp_sol):
        return (Vresp**2 * (z / q**2)) / (R0_KPC**2 + (z / q) ** 2)

    # Density band equivalent uses same Kz(q) map with q from rho bounds.
    fig, ax = plt.subplots(figsize=(7.4, 4.6))
    ax.plot(z, Kz(q_th), color="C0", lw=2.0, label=rf"theory $q={q_th:.2f}$")
    ax.plot(z, Kz(q_fit), color="C1", lw=1.8, ls="--", label=rf"Gaia best-fit $q={q_fit:.3f}$")
    # 1σ band from density
    lo = Kz(q_hi)
    hi = Kz(q_lo)
    ax.fill_between(z, lo, hi, color="C0", alpha=0.15, label=r"Gaia $1\sigma$-equivalent band")
    ax.set_xlabel(r"$|z|$ [kpc]")
    ax.set_ylabel(r"$K_z(R_0,z)$ [(km s$^{-1}$)$^2$ kpc$^{-1}$]")
    ax.set_title("Vertical-force visualization at fixed radial normalization")
    ax.legend(frameon=False, fontsize=9)
    fig.tight_layout()
    fig.savefig(OUT / "gaia_q080_theory_vs_bestfit.png", dpi=160)
    plt.close(fig)

    qs = np.linspace(0.55, 1.05, 200)
    rhos = np.array([rho_eff(q) for q in qs])
    fig, ax = plt.subplots(figsize=(7.0, 4.4))
    ax.plot(qs, rhos, color="C0", lw=2)
    ax.axhline(rho_gaia, color="k", ls=":", label="Gaia central")
    ax.axhspan(rho_lo, rho_hi, color="0.5", alpha=0.2, label=r"Gaia $1\sigma$")
    ax.axvline(q_th, color="C0", ls="--", label=rf"$q_{{\rm th}}={q_th:.2f}$")
    ax.axvline(q_fit, color="C1", ls="--", label=rf"$q_{{\rm fit}}={q_fit:.3f}$")
    ax.set_xlabel(r"$q$")
    ax.set_ylabel(r"$\rho_{\mathrm{eff}}$ [$M_\odot\,\mathrm{pc}^{-3}$]")
    ax.set_title("Oblate geometry ↔ near-plane equivalent density")
    ax.legend(frameon=False, fontsize=9)
    fig.tight_layout()
    fig.savefig(OUT / "gaia_q080_density_mapping.png", dpi=160)
    plt.close(fig)

    # Rotation comparison overview
    fig, ax = plt.subplots(figsize=(8.0, 4.6))
    ax.plot(R_grid, Vc_btfr, label="Response BTFR", lw=2)
    ax.plot(R_grid, Vb_grid, label="Baryons", lw=1.4, ls="--")
    ax.plot(R_grid, V_resp_btfr, label="Response only", lw=1.4, ls=":")
    ax.axhline(VQ, color="0.5", ls=":", label=rf"$V_Q={VQ:.1f}$")
    ax.set_xlim(1, 30)
    ax.set_xlabel(r"$R$ [kpc]")
    ax.set_ylabel(r"$V$ [km s$^{-1}$]")
    ax.legend(frameon=False)
    ax.set_title("Radial response realization")
    fig.tight_layout()
    fig.savefig(OUT / "paper3_radial_rotation_comparison.png", dpi=160)
    plt.close(fig)

    # CSVs / summary JSON
    with open(OUT / "paper3_gaia_radial_quantitative.csv", "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["model", "chi2_12bins", "RMS_residual_km_s"])
        w.writerow(["Response: BTFR normalization", f"{chi_btfr}", f"{rms_btfr}"])
        w.writerow(["Response: Solar normalization", f"{chi_sol}", f"{rms_sol}"])
        w.writerow(["MOND/RAR", f"{chi_rar}", f"{rms_rar}"])

    with open(OUT / "gaia_theory_q080_vs_bestfit.csv", "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(
            [
                "case",
                "q",
                "rho_eff_Msun_pc3",
                "offset_from_Gaia_sigma",
                "fractional_RMS_Kz_0_to_1p2kpc",
            ]
        )
        # fractional RMS of Kz theory vs best-fit over 0-1.2 kpc
        Kth, Kfit = Kz(q_th), Kz(q_fit)
        frac_rms = float(np.sqrt(np.mean(((Kth - Kfit) / np.maximum(Kfit, 1e-12)) ** 2)))
        w.writerow(["theory q_th", f"{q_th}", f"{rho_th}", f"{offset_sigma}", f"{frac_rms}"])
        w.writerow(["Gaia best fit", f"{q_fit}", f"{rho_gaia}", "0.0", "0.0"])

    summary = {
        "Mb_msun": Mb,
        "VQ_kms": VQ,
        "T_R0": T_R0,
        "V_resp_R0_btfr": V_resp_R0,
        "Vb_R0_adopted": Vb_adopted,
        "Vc_R0_btfr": Vc_R0,
        "VQ_solar": VQ_sol,
        "a0_eff": a0_eff,
        "V_resp_solar": V_resp_sol,
        "q_th": q_th,
        "q_fit": q_fit,
        "rho_eff_th": rho_th,
        "offset_sigma": offset_sigma,
        "q_interval": [q_lo, q_hi],
        "chi2_btfr": chi_btfr,
        "rms_btfr": rms_btfr,
        "chi2_solar": chi_sol,
        "rms_solar": rms_sol,
        "chi2_rar": chi_rar,
        "rms_rar": rms_rar,
        "ratio_5": float(np.interp(5.0, R_grid, ratio)),
        "ratio_R0": float(np.interp(R0_KPC, R_grid, ratio)),
        "ratio_30": float(np.interp(30.0, R_grid, ratio)),
        "component_masses": {
            "thin": M_thin,
            "thick": M_thick,
            "HI": M_hi,
            "H2": M_h2,
            "bulge": M_bulge,
        },
    }
    (OUT / "paper3_experiment_summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print("\nWrote figures + CSV/JSON into", OUT)


if __name__ == "__main__":
    main()
