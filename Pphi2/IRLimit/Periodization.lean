/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Periodization: Re-export from gaussian-field

The periodization CLM `𝓢(ℝ) →L[ℝ] C∞(S¹_L)` is defined in
`SchwartzNuclear.Periodization` in the gaussian-field package.
This file re-exports it for use in pphi2's IR limit.
-/

import SchwartzNuclear.Periodization

namespace Pphi2

-- Re-export periodizeCLM from gaussian-field
open GaussianField

end Pphi2
