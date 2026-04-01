/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Root module for the in-repo `Common` Lean library (Lake `lean_lib Common`).

Downstream libraries (e.g. `Pphi2`) import `Common.Mathlib.*` modules directly; this root
pulls the Gaussian / Cameron-Martin toolkit and the shared QFT formulation-layer
interfaces into the build graph so `lake build Common` succeeds.
-/
import Common.QFT.Euclidean.Formulations
import Common.QFT.Euclidean.ReconstructionInterfaces
