#!/usr/bin/env python3
"""Numerical sanity check of the closed-form solution u_f (Saxe Eq. u_soln).

Confirms, over many random (s, tau, u0, t) in the regime 0 < u0 < s, 0 < tau,
that
  * u_f(0) = u0, and
  * tau * u_f'(t) = 2 * u_f(t) * (s - u_f(t))      (Saxe Eq. sigmoidal_dyn),
the derivative taken by central finite difference. This is the empirical
pre-check behind the Lean theorems in DlnDynamics/ClosedForm.lean.

Pure standard library (math, random) -- no third-party dependencies.
"""
import math
import random


def uf(s, tau, u0, t):
    e = math.exp(2 * s * t / tau)
    return s * e / (e - 1 + s / u0)


def main():
    rng = random.Random(0)
    h = 1e-6
    max_init_err = 0.0
    max_ode_err = 0.0
    for _ in range(2000):
        u0 = rng.uniform(0.01, 1.0)
        s = u0 + rng.uniform(0.01, 2.0)          # enforce 0 < u0 < s
        tau = rng.uniform(0.3, 3.0)
        t = rng.uniform(-1.5, 4.0)
        max_init_err = max(max_init_err, abs(uf(s, tau, u0, 0.0) - u0))
        deriv = (uf(s, tau, u0, t + h) - uf(s, tau, u0, t - h)) / (2 * h)
        residual = tau * deriv - 2 * uf(s, tau, u0, t) * (s - uf(s, tau, u0, t))
        max_ode_err = max(max_ode_err, abs(residual))

    print(f"max |u_f(0) - u0|  = {max_init_err:.3e}")
    print(f"max ODE residual   = {max_ode_err:.3e}")
    assert max_init_err < 1e-12, "initial condition u_f(0)=u0 violated"
    assert max_ode_err < 1e-4, "ODE residual too large"
    print("OK: u_f(0)=u0 and tau*u_f' = 2*u_f*(s-u_f) hold numerically.")


if __name__ == "__main__":
    main()
