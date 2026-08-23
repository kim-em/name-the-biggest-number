/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Contenders.Contender1

/-- Submitted by Kim Morrison. -/
def contender_2 : Nat := 2

theorem contender_1_lt_contender_2 : contender_1 < contender_2 := by
  norm_num [contender_1, contender_2]
