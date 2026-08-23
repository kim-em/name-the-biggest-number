/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Contenders.Contender0

/-- Submitted by Kim Morrison. -/
def contender_1 : Nat := 1

theorem contender_0_lt_contender_1 : contender_0 < contender_1 := by
  norm_num [contender_0, contender_1]
