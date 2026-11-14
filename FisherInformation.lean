/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FisherInformation.KLFinite
public import FisherInformation.KLIntegral
public import FisherInformation.KLDivBridge
public import FisherInformation.KLFiniteDirectional
public import FisherInformation.KLIntegralDirectionalFDeriv
public import FisherInformation.FiniteRiemannian

/-!
# Fisher information from KL curvature and scores

Finite and integral Fisher identities, a density-to-measure KL bridge, line-directional
variants, and smooth finite score metrics under explicit regularity hypotheses.
Examples are an opt-in import.
-/

@[expose] public section
