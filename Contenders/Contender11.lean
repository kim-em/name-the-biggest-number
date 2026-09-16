/-
Copyright (c) 2026 Aristotle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Contender 11: Bigrand Extremexul

An implementation of Lawrence Hollom's *hyperfactorial array notation* (HAN) and of the
number **Bigrand Extremexul**

  `((...((200![1(1)[₂200,200,200,200]])![1(1)[₂200,200,200,200]])...)![1(1)[₂200,200,200,200]]`

with *Grand Extremexul* many parentheses, where Grand Extremexul is the same iteration
with *Extremexul* many parentheses and Extremexul is `200![1(1)[₂200,200,200,200]]`.

Hollom's rules, as published, are a rewriting system whose termination is a (wide open)
ordinal-analysis problem, and several of the published clauses are ambiguous.  What is
implemented below is a *precise reading* of the rules, made total by evaluating with a
(gigantic) step budget:

* `HAN.ar k a b` is `a ↑^k b` (with `↑^0` multiplication), and `HAN.hfact m n` is the basic
  hyperfactorial `n ↑^m (n-1) ↑^m ⋯ ↑^m 2`.
* Arrays (`HAN.Arr`) are lists of entries; each entry carries the separator that precedes it
  (`0` = comma, `a` = the separator `(a)`), and each entry is either a positive integer or a
  bracketed sub-array carrying a *bracket type* (`1` = the universal brackets `[ ]`,
  `2` = Hollom's type-2 brackets `[₂ ]`, …).
* `HAN.eval` implements, in Hollom's order, the rules `R1` (linear climbing), `R2`
  (separator climbing), `R3` (iteration on the main entry), `R4` (work inside a sub-array),
  `S1` (`[1] = n`), `S2` (trailing ones are dropped), and the type-2 bracket rule
  (`[ₖ₊₁1]` unfolds to `n` nested copies of the enclosing type-`k` bracket).
* `HAN.eval` takes a step budget; when the budget runs out the current base is returned,
  so the computed value is a *lower* approximation of the ideal value.  The budget used for
  the contender is itself a hyperfactorial-array value, so it is unimaginably larger than
  anything the evaluation can consume in practice.
-/

namespace HAN

/-! ## Hyperoperations and the basic hyperfactorial -/

/-- `ar k a b = a ↑^k b`, the `k`-th hyperoperation above multiplication:
`ar 0 a b = a * b`, `ar 1 a b = a ^ b`, `ar 2 a b = a ↑↑ b`, … -/
def ar : Nat → Nat → Nat → Nat
  | 0, a, b => a * b
  | _ + 1, _, 0 => 1
  | k + 1, a, b + 1 => ar k a (ar (k + 1) a b)

/-- `hfact m n = n ↑^m (n-1) ↑^m ⋯ ↑^m 2`, Hollom's `n!m`. -/
def hfact (m : Nat) : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => ar m (n + 2) (hfact m (n + 1))

/-! ## Arrays -/

mutual

/-- An entry of a hyperfactorial array: either a positive integer, or a bracketed sub-array
together with its bracket type (`1` = universal brackets, `k+1` = type-`k+1` brackets). -/
inductive Entry where
  | num : Nat → Entry
  | sub : Nat → Arr → Entry
  deriving Inhabited

/-- A hyperfactorial array: a list of entries, each tagged with the separator preceding it
(`0` for a comma, `a` for the separator `(a)`).  The tag of the first entry is ignored. -/
inductive Arr where
  | nil : Arr
  | cons : Nat → Entry → Arr → Arr
  deriving Inhabited

end

/-- Is the entry the number `1`? -/
def Entry.isOne : Entry → Bool
  | .num 1 => true
  | _ => false

/-- Does the array consist of ones only (so that it collapses to the base, rule `S1`)? -/
def Arr.allOnes : Arr → Bool
  | .nil => true
  | .cons _ e r => e.isOne && r.allOnes

mutual

/-- Is the deepest main entry of this entry a number `≥ 2`? -/
def Entry.deepBig : Entry → Bool
  | .num k => 2 ≤ k
  | .sub _ a => a.deepBig

/-- Is the deepest main entry of this array a number `≥ 2`?  (Rule `R3` applies then.) -/
def Arr.deepBig : Arr → Bool
  | .nil => false
  | .cons _ e _ => e.deepBig

end

mutual

/-- Decrease the deepest main entry by one. -/
def Entry.decMain : Entry → Entry
  | .num k => .num (k - 1)
  | .sub t a => .sub t a.decMain

/-- Decrease the deepest main entry of the array by one. -/
def Arr.decMain : Arr → Arr
  | .nil => .nil
  | .cons s e r => .cons s e.decMain r

end

mutual

/-- Replace the deepest main entry by `1` (the `▮k ↦ ▮1` of rule `R1`). -/
def Entry.mainToOne : Entry → Entry
  | .num _ => .num 1
  | .sub t a => .sub t a.mainToOne

/-- Replace the deepest main entry of the array by `1`. -/
def Arr.mainToOne : Arr → Arr
  | .nil => .nil
  | .cons s e r => .cons s e.mainToOne r

end

/-- Drop trailing ones (rule `S2`). -/
def Arr.crop : Arr → Arr
  | .nil => .nil
  | .cons s e r =>
    match r.crop with
    | .nil => if e.isOne then .nil else .cons s e .nil
    | r' => .cons s e r'

/-- Index of the active entry: the first entry that is not the number `1`. -/
def Arr.activeIdx : Arr → Option Nat
  | .nil => none
  | .cons _ e r => if e.isOne then (r.activeIdx).map (· + 1) else some 0

/-- The entry at a given index. -/
def Arr.entryAt : Arr → Nat → Option Entry
  | .nil, _ => none
  | .cons _ e _, 0 => some e
  | .cons _ _ r, i + 1 => r.entryAt i

/-- The separator in front of the entry at a given index. -/
def Arr.sepAt : Arr → Nat → Nat
  | .nil, _ => 0
  | .cons s _ _, 0 => s
  | .cons _ _ r, i + 1 => r.sepAt i

/-- Replace the entry at a given index. -/
def Arr.setEntry : Arr → Nat → Entry → Arr
  | .nil, _, _ => .nil
  | .cons s _ r, 0, x => .cons s x r
  | .cons s e r, i + 1, x => .cons s e (r.setEntry i x)

/-- `chainAux sep x c` is `c` further copies of `x`, each preceded by the separator `(sep)`. -/
def chainAux (sep : Nat) (x : Entry) : Nat → Arr
  | 0 => .nil
  | c + 1 => .cons sep x (chainAux sep x c)

/-- `chain c sep x` is the array of `c` copies of the entry `x`, separated by `(sep)`. -/
def chain (c sep : Nat) (x : Entry) : Arr :=
  match c with
  | 0 => .nil
  | c + 1 => .cons 0 x (chainAux sep x c)

/-- The `n`-fold nesting used by the type-`k+1` bracket rule: the entry at index `i` of `A`
is replaced by a type-`t` bracket holding `A` with that entry replaced by the next nesting
level, `n` times over, the innermost level holding the number `1`. -/
def omegaNest (t : Nat) (A : Arr) (i : Nat) : Nat → Entry
  | 0 => .sub t (A.setEntry i (.num 1))
  | j + 1 => .sub t (A.setEntry i (omegaNest t A i j))

/-- One rewriting step of the array `A` (sitting inside brackets of type `t`) at base `n`.
`none` means that no rule applies, i.e. the array consists of ones only.  The first argument
is a budget for descending into sub-arrays (rule `R4`). -/
def reduceStep : Nat → Nat → Nat → Arr → Option Arr
  | 0, _, _, _ => none
  | d + 1, n, t, A =>
    match A.activeIdx with
    | none => none
    | some i =>
      match A.entryAt i with
      | none => none
      | some e =>
        match e with
        | .sub t' B =>
          if B.allOnes then
            -- `S1`, or the type-`t'` bracket rule when the bracket type is higher than the
            -- ambient one.
            if t < t' then some (A.setEntry i (omegaNest t A i n))
            else some (A.setEntry i (.num n))
          else if B.deepBig then
            climb n t A i e
          else
            -- `R4`: work inside the sub-array.
            match reduceStep d n t' B with
            | some B' => some (A.setEntry i (.sub t' B'))
            | none => none
        | .num _ => climb n t A i e
where
  /-- Rules `R1` and `R2`: the active entry at index `i` is decreased, and the receiving
  entry in front of it is filled in. -/
  climb (n t : Nat) (A : Arr) (i : Nat) (e : Entry) : Option Arr :=
    match i with
    | 0 => none
    | j + 1 =>
      let Adec := A.setEntry (j + 1) e.decMain
      let Aone := A.setEntry (j + 1) e.mainToOne
      let s := A.sepAt (j + 1)
      let recv : Entry :=
        match s with
        | 0 => .sub t Aone
        | a + 1 => .sub t (chain n a (.sub t Adec))
      some (Adec.setEntry j recv)

/-- `eval f n t A` is the value of `n![A]`, where `A` sits inside brackets of type `t`,
computed with a step budget of `f`.  When the budget is exhausted the base `n` is returned. -/
def eval : Nat → Nat → Nat → Arr → Nat
  | 0, n, _, _ => n
  | f + 1, n, t, A =>
    let A := A.crop
    if A.allOnes then
      -- `[1] = n`, so `n![1] = n!n`.
      hfact n n
    else if A.deepBig then
      -- `R3`: iterate the map `a ↦ a![A with main entry decreased]`, `n` times, from `n`.
      (fun a => eval f a t A.decMain)^[n] n
    else
      match reduceStep f n t A with
      | some A' => eval f n t A'
      | none => hfact n n

/-! ## Extremexul, Grand Extremexul, Bigrand Extremexul -/

/-- The array `[200,200,200,200]`. -/
def fourHundreds : Arr :=
  .cons 0 (.num 200) (.cons 0 (.num 200) (.cons 0 (.num 200) (.cons 0 (.num 200) .nil)))

/-- Hollom's array `[1(1)[₂200,200,200,200]]`. -/
def extremexulArr : Arr :=
  .cons 0 (.num 1) (.cons 1 (.sub 2 fourHundreds) .nil)

/-- `extremexulStep f x = x![1(1)[₂200,200,200,200]]`, evaluated with budget `f`. -/
def extremexulStep (f x : Nat) : Nat := eval f x 1 extremexulArr

/-- Extremexul, `200![1(1)[₂200,200,200,200]]`, evaluated with budget `f`. -/
def extremexul (f : Nat) : Nat := extremexulStep f 200

/-- Grand Extremexul: `extremexulStep` iterated Extremexul times, starting from `200`. -/
def grandExtremexul (f : Nat) : Nat := (extremexulStep f)^[extremexul f] 200

/-- Bigrand Extremexul: `extremexulStep` iterated Grand Extremexul times, from `200`. -/
def bigrandExtremexul (f : Nat) : Nat := (extremexulStep f)^[grandExtremexul f] 200

end HAN

/-- **Bigrand Extremexul**, evaluated with a step budget which is itself a hyperfactorial
array value (so, far beyond any budget the evaluation could exhaust). -/
def contender_11 : Nat :=
  HAN.bigrandExtremexul (HAN.bigrandExtremexul (HAN.ar 4 10 10))
