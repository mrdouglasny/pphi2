#!/usr/bin/env python3
"""Empirical 2-slice two-point check of the asym transfer-operator normalization.

Question: does `asymTransferOperatorCLM` (weight exp(-(a/2)*spatialAction)) reproduce
the two-point function of `latticeGaussianMeasureAsym`, or is the weight off by a
factor of `a` (should it be exp(-(a^2/2)*spatialAction))?

Setup: FREE theory (P=0), Nt=2 time slices, Ns=1 spatial site. Then a single time
slice is one real variable phi in R; the transfer operator acts on L^2(R, Lebesgue).

  - spatialAction(phi) = spatialKinetic + spatialPotential.
      spatialKinetic = (1/2) sum_x a^-2 (phi(x+1)-phi(x))^2 = 0  for Ns=1 (periodic, x+1=x).
      spatialPotential = sum_x (1/2 m^2 phi_x^2 + wickPoly) = 1/2 m^2 phi^2  (P=0).
    so spatialAction(phi) = (1/2) m^2 phi^2.
  - transferWeight     w(phi) = exp(-(coef/2) * spatialAction) = exp(-(coef*m^2/4) phi^2),
    where coef = a in the CODE, coef = a^2 is the CLAIMED-correct value.
  - transferGaussian   G(u)   = exp(-timeCoupling(0,u)) = exp(-(1/2) u^2).
  - transfer kernel     T(phi,phi') = w(phi) G(phi-phi') w(phi'),  on L^2(R, dphi).

Measure side (pphi2 convention, cross-checked against wickConstantAsym):
  covariance  C = (L_graph + a^2 m^2 I)^{-1},  L_graph = graph Laplacian of the
  Nt=2 time cycle (x-direction trivial). L_graph = [[2,-2],[-2,2]] (eigenvalues 0,4).
  <phi_0^2>   = C_00,   <phi_0 phi_1> = C_01.

Two-slice (Nt=2) transfer predictions (periodic trace):
  Z            = Tr(T^2)            = sum_ij T_ij^2
  <phi_0^2>    = Tr(Phi^2 T^2)/Z    = sum_ij phi_i^2 T_ij^2 / Z
  <phi_0 phi_1>= Tr(Phi T Phi T)/Z  = sum_ij phi_i phi_j T_ij^2 / Z      (Phi = diag(phi))

We build T as a quadrature matrix on a phi-grid and compare to the measure for both
coef = a and coef = a^2.
"""
import numpy as np

def measure_two_point(a, m):
    """pphi2 GFF covariance for Nt=2, Ns=1:  C = (L_graph + a^2 m^2 I)^{-1}."""
    L = np.array([[2.0, -2.0], [-2.0, 2.0]])          # 2-cycle graph Laplacian
    C = np.linalg.inv(L + (a * a * m * m) * np.eye(2))
    return C[0, 0], C[0, 1]

def transfer_two_point(a, m, coef, grid_half=8.0, n=2001):
    """Numerical transfer-operator prediction with weight exp(-(coef/2)*spatialAction)."""
    phi = np.linspace(-grid_half, grid_half, n)
    dphi = phi[1] - phi[0]
    w = np.exp(-(coef * m * m / 4.0) * phi**2)        # w(phi) = exp(-(coef*m^2/4) phi^2)
    diff = phi[:, None] - phi[None, :]
    G = np.exp(-0.5 * diff**2)                        # G(phi-phi') = exp(-1/2 (phi-phi')^2)
    T = (w[:, None] * G * w[None, :]) * dphi          # kernel * quadrature weight
    T2 = T * T                                        # T_ij T_ji = T_ij^2 (T symmetric)
    Z = T2.sum()
    var = (phi[:, None]**2 * T2).sum() / Z            # <phi_0^2>
    cov = (phi[:, None] * phi[None, :] * T2).sum() / Z  # <phi_0 phi_1>
    return var, cov

def cycle_laplacian(n):
    """Graph Laplacian of the n-cycle: 2I - (P + P^{-1}), P = cyclic shift.
    n=1 -> [[0]]; n=2 -> [[2,-2],[-2,2]] (double edge)."""
    P = np.roll(np.eye(n), 1, axis=0)
    return 2 * np.eye(n) - (P + P.T)

def precision_check(Nt, Ns, a, m, coef):
    """General (Nt,Ns) precision-matrix comparison (covers the spatialKinetic term).

    Measure precision:  P_meas = L_t⊗I_s + I_t⊗L_s + a^2 m^2 I        (= a^2 Q).
    Transfer precision: P_tr   = L_t⊗I_s + coef·(a^-2 I_t⊗L_s + m^2 I)
       (time coupling: L_t⊗I_s, coeff 1; w^2 per slice: coef·(spatialKinetic+½m²)
        Hessian = coef·(a^-2 L_s + m^2 I) per slice).
    They are equal iff coef = a^2 (the spatial-kinetic AND mass coeffs both need a^2)."""
    Lt, Ls = cycle_laplacian(Nt), cycle_laplacian(Ns)
    It, Is = np.eye(Nt), np.eye(Ns)
    L_t = np.kron(Lt, Is); L_s = np.kron(It, Ls); I = np.eye(Nt * Ns)
    P_meas = L_t + L_s + (a * a * m * m) * I
    P_tr = L_t + coef * ((1.0 / (a * a)) * L_s + m * m * I)
    return np.allclose(P_meas, P_tr)

def main():
    print("=" * 74)
    print("General precision-matrix check (exercises spatialKinetic, Ns>=2)")
    print("=" * 74)
    for Nt, Ns, a, m in [(2, 2, 0.5, 1.0), (3, 2, 0.7, 1.3), (4, 3, 0.5, 1.0)]:
        ok_a = precision_check(Nt, Ns, a, m, coef=a)
        ok_a2 = precision_check(Nt, Ns, a, m, coef=a * a)
        print(f"  Nt={Nt} Ns={Ns} a={a} m={m}:  coef=a match={ok_a}   "
              f"coef=a^2 match={ok_a2}")
    print("\n" + "=" * 74)
    print("2-slice (Nt=2, Ns=1) two-point: measure vs transfer operator")
    print("=" * 74)
    for a, m in [(0.5, 1.0), (2.0, 1.0), (1.0, 1.0), (0.3, 1.7)]:
        mv, mc = measure_two_point(a, m)
        va, ca = transfer_two_point(a, m, coef=a)      # CODE weight: coef = a
        v2, c2 = transfer_two_point(a, m, coef=a * a)  # CLAIMED-correct: coef = a^2
        print(f"\n--- a={a}, m={m}   (a^2 m^2={a*a*m*m:.4f}, a m^2={a*m*m:.4f}) ---")
        print(f"  measure          <phi_0^2>={mv:.6f}   <phi_0 phi_1>={mc:.6f}")
        print(f"  transfer coef=a  <phi_0^2>={va:.6f}   <phi_0 phi_1>={ca:.6f}"
              f"   match={np.allclose([va,ca],[mv,mc],atol=1e-3)}")
        print(f"  transfer coef=a^2<phi_0^2>={v2:.6f}   <phi_0 phi_1>={c2:.6f}"
              f"   match={np.allclose([v2,c2],[mv,mc],atol=1e-3)}")
    print("\n" + "=" * 74)
    print("VERDICT: coef=a^2 reproduces the measure; coef=a (the code) does not")
    print("(they coincide only at a=1). The transfer weight should be exp(-(a^2/2)*S).")
    print("=" * 74)

if __name__ == "__main__":
    main()
