"""Issue #63 check: is E[exp(-2V)] bounded uniformly in a in (0,1] at FIXED N?

Setting: d = 2, P(x) = x^4/4 (the admissible pure quartic: InteractionPolynomial fixes the
leading coefficient to 1/n), lattice GFF on (Z/N)^2 with spacing a, GJ normalization
(covariance (a^d (-Delta_a + m^2))^{-1}), V = a^d sum_x (1/4) :phi_x^4:_c, c = wickConstant.

Zero mode: phibar = N^{-d} sum_x phi_x has variance s0 = 1/(L^d m^2), L = N a.
Wick ordering commutes with conditional expectation, so
    E[V | phibar] = (L^d/4) :phibar^4:_{s0} = lam * H4(Z),   lam = 1/(4 L^d m^4),
with Z ~ N(0,1), H4(z) = z^4 - 6 z^2 + 3.  Conditional Jensen then gives, for EVERY N,
    E[exp(-2V)] >= J(lam) := E[exp(-2 lam H4(Z))],
with equality at N = 1 (single site: V = lam H4(Z) exactly). For N > 1 this script evaluates
only the one-dimensional lower bound J(lam), not the full lattice integral.

Rigorous floor: H4 = (z^2-3)^2 - 6 <= -23/4 on |z^2-3| <= 1/2, so
    J(lam) >= P(|Z^2-3| <= 1/2) * exp(11.5 lam)  -> infinity as lam -> infinity (a -> 0).
"""
import math

def logJ(lam, n=400000, R=12.0):
    # log E[exp(-2 lam H4(Z))], factoring out the max exp(12 lam) at z^2 = 3 (Simpson, pure Python)
    f = lambda z: math.exp(-2*lam*((z*z-3)**2) - z*z/2) / math.sqrt(2*math.pi)
    h = 2*R/n
    s = f(-R) + f(R) + sum((4 if i % 2 else 2)*f(-R + i*h) for i in range(1, n))
    return 12*lam + math.log(s*h/3)

p_floor = math.erf(math.sqrt(3.5/2)) - math.erf(math.sqrt(2.5/2))
m, d = 1.0, 2
print(f"d={d}, mass={m}, P=x^4/4.  P(|Z^2-3|<=1/2) = {p_floor:.6f}")
print(f"{'N':>3} {'a':>8} {'L=Na':>8} {'lam':>10} {'log J(lam)':>12} {'floor':>12}  (log E[e^-2V] >= log J; = at N=1)")
for N in (1, 4, 16):
    for a in (1.0, 0.5, 0.25, 0.1, 0.05, 0.01):
        L = N*a
        lam = 1.0/(4 * L**d * m**4)
        print(f"{N:>3} {a:>8.3f} {L:>8.3f} {lam:>10.3f} {logJ(lam):>12.3f} "
              f"{math.log(p_floor)+11.5*lam:>12.3f}")
