-- Pphi2: Formal construction of P(Φ)₂ via stochastic quantization
-- Following Duch-Dybalski-Jahandideh (arXiv:2311.04137)
-- On the cylinder ℝ × S¹_L (adapted from spheres S_R)

-- Core definitions
import Pphi2.Basic
import Pphi2.Polynomial
import Pphi2.OSAxioms

-- Function spaces
import Pphi2.FunctionSpaces.WeightedLp
import Pphi2.FunctionSpaces.Embedding

-- Gaussian theory on the cylinder
import Pphi2.GaussianCylinder.Covariance

-- P(Φ)₂ measure on the cylinder
import Pphi2.MeasureCylinder.Regularized
import Pphi2.MeasureCylinder.UVLimit

-- Stochastic quantization
import Pphi2.StochasticQuant.DaPratoDebussche

-- Stochastic estimates
import Pphi2.StochasticEst.InfiniteVolumeBound

-- Energy estimate
import Pphi2.Energy.EnergyEstimate

-- Infinite volume limit
import Pphi2.InfiniteVolume.Tightness

-- Integrability / OS regularity
import Pphi2.Integrability.Regularity

-- Reflection positivity
import Pphi2.ReflectionPositivity.RPPlane

-- Euclidean invariance
import Pphi2.EuclideanInvariance.Invariance

-- Main theorem
import Pphi2.Main
