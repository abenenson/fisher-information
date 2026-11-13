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

/-!
# Fisher information from KL curvature and scores

Finite and integral Fisher identities, a density-to-measure KL bridge, and line-directional
variants under explicit analytic regularity hypotheses. Examples are an opt-in import.
-/

@[expose] public section
