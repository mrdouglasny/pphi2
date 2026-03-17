-- Pphi2: Formal construction of P(Φ)₂ Euclidean QFT
-- Approach: Glimm-Jaffe/Nelson lattice construction with continuum limit
-- See plan.md for the development roadmap.

-- Core definitions
import Pphi2.Polynomial

-- Phase 1: Wick ordering
import Pphi2.WickOrdering.WickPolynomial
import Pphi2.WickOrdering.Counterterm

-- Phase 1: Interacting measure (general + lattice)
import Pphi2.InteractingMeasure.General
import Pphi2.InteractingMeasure.LatticeAction
import Pphi2.InteractingMeasure.LatticeMeasure
import Pphi2.InteractingMeasure.Normalization

-- Phase 2: Transfer matrix and reflection positivity
import Pphi2.TransferMatrix.TransferMatrix
import Pphi2.TransferMatrix.L2Operator
import Pphi2.TransferMatrix.Jentzsch
import Pphi2.TransferMatrix.Positivity
import Pphi2.OSProofs.OS3_RP_Lattice
import Pphi2.OSProofs.OS3_RP_Inheritance

-- Phase 3: Spectral gap and clustering (OS4)
import Pphi2.TransferMatrix.SpectralGap
import Pphi2.OSProofs.OS4_MassGap
import Pphi2.OSProofs.OS4_Ergodicity

-- Phase 4: Continuum limit
import Pphi2.ContinuumLimit.Embedding
import Pphi2.ContinuumLimit.Tightness
import Pphi2.ContinuumLimit.Convergence
import Pphi2.ContinuumLimit.AxiomInheritance

-- Phase 4b: Torus continuum limit (Gaussian)
import Pphi2.TorusContinuumLimit.TorusEmbedding
import Pphi2.TorusContinuumLimit.TorusPropagatorConvergence
import Pphi2.TorusContinuumLimit.TorusTightness
import Pphi2.TorusContinuumLimit.TorusConvergence
import Pphi2.TorusContinuumLimit.TorusGaussianLimit
import Pphi2.TorusContinuumLimit.TorusInteractingLimit
import Pphi2.TorusContinuumLimit.TorusOSAxioms
import Pphi2.TorusContinuumLimit.TorusInteractingOS

-- Phase 4c: Cylinder continuum limit (Gaussian + interacting)
import Pphi2.CylinderContinuumLimit.CylinderInteraction
import Pphi2.CylinderContinuumLimit.CylinderHypercontractivity
import Pphi2.CylinderContinuumLimit.CylinderUVRemoval
import Pphi2.CylinderContinuumLimit.CylinderIRRemoval
import Pphi2.CylinderContinuumLimit.CylinderInteractingOS
import Pphi2.CylinderContinuumLimit.CylinderOSAxioms

-- Phase 5: Euclidean invariance (OS2)
import Pphi2.OSProofs.OS2_WardIdentity

-- Phase 6: Assembly — OS axiom framework and main theorem
import Pphi2.OSAxioms
import Pphi2.Main
