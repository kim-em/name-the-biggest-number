/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Contenders.Contender3

/-- Submitted by Kim Morrison. -/
def contender_4 : Nat := 42

theorem contender_3_lt_contender_4 : contender_3 < contender_4 := by
  norm_num [contender_3, contender_4]
