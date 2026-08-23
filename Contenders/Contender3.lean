/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Contenders.Contender2

/-- Submitted by Kim Morrison. -/
def contender_3 : Nat := 2 * 2

theorem contender_2_lt_contender_3 : contender_2 < contender_3 := by
  norm_num [contender_2, contender_3]
