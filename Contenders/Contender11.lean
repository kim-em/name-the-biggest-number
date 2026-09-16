import Mathlib
import Contenders.Contender10


/-!
# The three-argument Veblen function

Mathlib provides the binary Veblen function `Ordinal.veblen`, whose values are cofinal in the
Feferman–Schütte ordinal `Γ₀`. Here we build the three-argument Veblen function `veblen3`, whose
values are cofinal in the (much larger) Ackermann ordinal:

* `veblen3 0 b c = veblen b c`;
* `veblen3 a b` for `a ≠ 0` is the `b`-th function of the Veblen hierarchy built over the function
  enumerating the common fixed points of `fun x ↦ veblen3 a' x 0` for all `a' < a`.

In particular `veblen3 1 0 0 = Γ₀`.
-/

namespace Contender11

open Order Ordinal Set

/-- The starting function of the `a`-th Veblen hierarchy: for `a = 0` it is `ω ^ ·`, and
otherwise it enumerates the common fixed points of `fun x ↦ veblen3 a' x 0` for `a' < a`. -/
noncomputable def vbase (a : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} :=
  if a = 0 then (ω ^ ·)
  else derivFamily fun (⟨x, _⟩ : Iio a) ↦ fun c ↦ veblenWith (vbase x) c 0
  termination_by a

/-- The three-argument Veblen function. -/
noncomputable def veblen3 (a b : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} :=
  veblenWith (vbase a) b

theorem vbase_zero : vbase 0 = (ω ^ ·) := by
  rw [vbase, if_pos rfl]

theorem vbase_of_ne_zero {a : Ordinal} (h : a ≠ 0) :
    vbase a = derivFamily fun x : Iio a ↦ fun c ↦ veblen3 x.1 c 0 := by
  rw [vbase, if_neg h]
  rfl

theorem veblen3_zero (b c : Ordinal) : veblen3 0 b c = veblen b c := by
  rw [veblen3, vbase_zero, veblen, veblenWith]

theorem isNormal_vbase (a : Ordinal) : IsNormal (vbase a) := by
  by_cases h : a = 0
  · subst h
    rw [vbase_zero]
    exact isNormal_opow one_lt_omega0
  · rw [vbase_of_ne_zero h]
    exact isNormal_derivFamily _

theorem isNormal_veblen3_zero_middle : IsNormal fun c ↦ veblen3 0 c 0 := by
  simpa only [veblen3_zero] using isNormal_veblen_zero

theorem vbase_zero_pos (a : Ordinal) : 0 < vbase a 0 := by
  by_cases h : a = 0
  · subst h
    rw [vbase_zero]
    simp
  · have h0 : (0 : Ordinal) < a := zero_lt_iff.mpr h
    have hfp := derivFamily_fp
      (f := fun x : Iio a ↦ fun c ↦ veblen3 x.1 c 0) (i := ⟨0, h0⟩)
      isNormal_veblen3_zero_middle 0
    rw [← vbase_of_ne_zero h, veblen3_zero] at hfp
    rw [← hfp]
    exact veblen_pos

theorem isNormal_veblen3 (a b : Ordinal) : IsNormal (veblen3 a b) :=
  isNormal_veblenWith (isNormal_vbase a) b

theorem veblen3_right_strictMono (a b : Ordinal) : StrictMono (veblen3 a b) :=
  veblenWith_right_strictMono (isNormal_vbase a) b

theorem veblen3_pos {a b c : Ordinal} : 0 < veblen3 a b c :=
  veblenWith_pos (isNormal_vbase a) (vbase_zero_pos a)

theorem isNormal_veblen3_middle (a : Ordinal) : IsNormal fun b ↦ veblen3 a b 0 :=
  isNormal_veblenWith_zero (isNormal_vbase a) (vbase_zero_pos a)

theorem veblen3_middle_strictMono (a : Ordinal) : StrictMono fun b ↦ veblen3 a b 0 :=
  (isNormal_veblen3_middle a).strictMono

/-- For `b₁ < b₂`, the value `veblen3 a b₂ c` is a fixed point of `veblen3 a b₁`. -/
theorem veblen3_veblen3_of_lt {a b₁ b₂ : Ordinal} (h : b₁ < b₂) (c : Ordinal) :
    veblen3 a b₁ (veblen3 a b₂ c) = veblen3 a b₂ c :=
  veblenWith_veblenWith_of_lt (isNormal_vbase a) h c

/-- For `a₁ < a₂`, the value `veblen3 a₂ b c` is a fixed point of `fun x ↦ veblen3 a₁ x 0`. -/
theorem veblen3_outer_fix {a₁ a₂ : Ordinal} (h : a₁ < a₂) (b c : Ordinal) :
    veblen3 a₁ (veblen3 a₂ b c) 0 = veblen3 a₂ b c := by
  have ha₂ : a₂ ≠ 0 := (h.trans_le (le_refl _)).ne_bot
  have hmem : veblen3 a₂ b c ∈ range (vbase a₂) :=
    veblenWith_mem_range (isNormal_vbase a₂)
  rw [vbase_of_ne_zero ha₂,
    mem_range_derivFamily (fun x : Iio a₂ ↦ isNormal_veblen3_middle x.1)] at hmem
  exact hmem ⟨a₁, h⟩

/-- Values of `veblen3` are powers of `ω`. -/
theorem veblen3_mem_range_opow (a b c : Ordinal) :
    veblen3 a b c ∈ range (ω ^ · : Ordinal → Ordinal) := by
  by_cases h : a = 0
  · subst h
    rw [veblen3_zero]
    exact veblen_mem_range_opow b c
  · have h0 : (0 : Ordinal) < a := zero_lt_iff.mpr h
    have hfix := veblen3_outer_fix h0 b c
    rw [veblen3_zero] at hfix
    rw [← hfix]
    exact veblen_mem_range_opow _ _

theorem veblen3_outer_strictMono_zero {a₁ a₂ : Ordinal} (h : a₁ < a₂) :
    veblen3 a₁ 0 0 < veblen3 a₂ 0 0 := by
  have hfix : veblen3 a₁ (veblen3 a₂ 0 0) 0 = veblen3 a₂ 0 0 := veblen3_outer_fix h 0 0
  have hpos : (0 : Ordinal) < veblen3 a₂ 0 0 := veblen3_pos
  calc veblen3 a₁ 0 0 < veblen3 a₁ (veblen3 a₂ 0 0) 0 := veblen3_middle_strictMono a₁ hpos
    _ = veblen3 a₂ 0 0 := hfix

/-- Comparison across the middle argument. -/
theorem veblen3_lt_veblen3_middle {a b₁ b₂ x y : Ordinal} (h : b₁ < b₂)
    (hx : x < veblen3 a b₂ y) : veblen3 a b₁ x < veblen3 a b₂ y :=
  (veblenWith_lt_veblenWith_iff (isNormal_vbase a)).2 (Or.inr (Or.inl ⟨h, hx⟩))

/-- Comparison across the outer argument. -/
theorem veblen3_lt_of_outer_lt {a₁ a₂ x b c : Ordinal} (h : a₁ < a₂) (hx : x < veblen3 a₂ b c) :
    veblen3 a₁ x 0 < veblen3 a₂ b c :=
  calc veblen3 a₁ x 0 < veblen3 a₁ (veblen3 a₂ b c) 0 := veblen3_middle_strictMono a₁ hx
    _ = veblen3 a₂ b c := veblen3_outer_fix h b c

/-- Values of `veblen3` are closed under successor. -/
theorem lt_veblen3_succ {a b c x : Ordinal} (hx : x < veblen3 a b c) (hpos : 0 < x) :
    x + 1 < veblen3 a b c := by
  obtain ⟨y, hy⟩ := veblen3_mem_range_opow a b c
  have hy' : veblen3 a b c = ω ^ y := hy.symm
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [opow_zero] at hy'
    rw [hy', Order.lt_one_iff] at hx
    exact absurd hx hpos.ne'
  have h1 : (1 : Ordinal) < ω ^ y := by
    calc (1 : Ordinal) = ω ^ (0 : Ordinal) := by simp
      _ < ω ^ y := (opow_lt_opow_iff_right one_lt_omega0).2 (zero_lt_iff.mpr hy0)
  rw [hy'] at hx ⊢
  exact isPrincipal_add_omega0_opow y hx h1

end Contender11


/-!
# A notation system for the ordinals below the Ackermann ordinal

`TNote` is a system of terms built from the three-argument Veblen function of
`Contenders.Contender11.Veblen3`: `TNote.node a b c d` denotes `φ(a, b, c) + d`, and `TNote.zero`
denotes `0`. Every term denotes an ordinal below the Ackermann ordinal `φ(1, 0, 0, 0)` via
`TNote.value`.

The point of the file is `TNote.fs`, which assigns to every nonzero term `t` and every natural
number `i` a term `fs t i` of strictly smaller value; on terms in normal form these are the
standard fundamental sequences of the Veblen hierarchy. `TNote.fs_value_lt` is the key fact that
makes the fast-growing hierarchy of `Contenders.Contender11.Hierarchy` well defined.
-/

namespace Contender11

open Order Ordinal

/-- Terms of a notation system for the ordinals below the Ackermann ordinal.
`node a b c d` denotes `φ(a, b, c) + d`, where `φ` is the three-argument Veblen function. -/
inductive TNote where
  /-- The term denoting the ordinal `0`. -/
  | zero : TNote
  /-- `node a b c d` denotes `φ(a, b, c) + d`. -/
  | node : TNote → TNote → TNote → TNote → TNote
  deriving DecidableEq

namespace TNote

/-- The ordinal denoted by a term. -/
noncomputable def value : TNote → Ordinal.{0}
  | zero => 0
  | node a b c d => veblen3 (value a) (value b) (value c) + value d

@[simp] theorem value_zero : value zero = 0 := rfl

@[simp] theorem value_node (a b c d : TNote) :
    value (node a b c d) = veblen3 a.value b.value c.value + d.value := rfl

theorem value_pos {t : TNote} (h : t ≠ zero) : 0 < t.value := by
  cases t with
  | zero => exact absurd rfl h
  | node a b c d => simpa using lt_of_lt_of_le veblen3_pos le_self_add

/-- The term denoting `1`. -/
def one : TNote := node zero zero zero zero

@[simp] theorem value_one : value one = 1 := by
  simp [one, veblen3_zero, veblen_zero_apply]

/-- Add one to a term, on the right. -/
def addOne : TNote → TNote
  | zero => one
  | node a b c d => node a b c (addOne d)

@[simp] theorem value_addOne (t : TNote) : (addOne t).value = t.value + 1 := by
  induction t with
  | zero => simp [addOne]
  | node a b c d _ _ _ ih => simp [addOne, ih, add_assoc]

/-- The term denoting the natural number `k`. -/
def finTerm : ℕ → TNote
  | 0 => zero
  | (k + 1) => node zero zero zero (finTerm k)

@[simp] theorem value_finTerm (k : ℕ) : (finTerm k).value = k := by
  induction k with
  | zero => simp [finTerm]
  | succ k ih =>
    simp only [finTerm, value_node, value_zero, veblen3_zero, veblen_zero_apply, opow_zero, ih]
    push_cast
    exact (Nat.cast_add_one_comm k).symm

/-- Whether a term is syntactically a successor, i.e. whether its last summand is `1`. -/
def isSucc : TNote → Bool
  | zero => false
  | node a b c d =>
    match d with
    | zero => decide (a = zero) && decide (b = zero) && decide (c = zero)
    | node w x y z => isSucc (node w x y z)

/-- The predecessor of a term whose last summand is `1`. -/
def pred : TNote → TNote
  | zero => zero
  | node a b c d =>
    match d with
    | zero => zero
    | node w x y z => node a b c (pred (node w x y z))

theorem value_pred {t : TNote} (h : isSucc t = true) : t.value = (pred t).value + 1 := by
  induction t with
  | zero => simp [isSucc] at h
  | node a b c d _ _ _ ih =>
    cases d with
    | zero =>
      simp only [isSucc, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      simp [pred, veblen3_zero, veblen_zero_apply]
    | node w x y z =>
      have h' : isSucc (node w x y z) = true := by simpa [isSucc] using h
      simp only [pred, value_node, ih h', ← add_assoc]

/-- `omegaPowMul b k` denotes `ω ^ b * k`. -/
def omegaPowMul (b : TNote) : ℕ → TNote
  | 0 => zero
  | (k + 1) => node zero zero b (omegaPowMul b k)

@[simp] theorem value_omegaPowMul (b : TNote) (k : ℕ) :
    (omegaPowMul b k).value = ω ^ b.value * k := by
  induction k with
  | zero => simp [omegaPowMul]
  | succ k ih =>
    simp only [omegaPowMul, value_node, value_zero, veblen3_zero, veblen_zero_apply, ih]
    push_cast
    rw [mul_add, mul_one, ← mul_one_add, ← mul_add_one, Nat.cast_add_one_comm k]

theorem omegaPowMul_zero_eq_finTerm (k : ℕ) : omegaPowMul zero k = finTerm k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [omegaPowMul, finTerm, ih]

/-- Iterating a term-level operation `k` times. -/
def nest (f : TNote → TNote) : TNote → ℕ → TNote
  | x, 0 => x
  | x, (k + 1) => nest f (f x) k

theorem nest_value_lt {f : TNote → TNote} {Y : Ordinal}
    (hf : ∀ x : TNote, x.value < Y → (f x).value < Y) :
    ∀ (k : ℕ) {x : TNote}, x.value < Y → (nest f x k).value < Y := by
  intro k
  induction k with
  | zero => intro x hx; simpa [nest] using hx
  | succ k ih => intro x hx; exact ih (hf x hx)

/-- The fundamental sequence assigned to a term: for every nonzero term `t`, `fs t i` is a term
of strictly smaller value (see `fs_value_lt`), and on terms in normal form this is the standard
fundamental sequence of the Veblen hierarchy. -/
def fs : TNote → ℕ → TNote
  | zero, _ => zero
  | node a b c d, i =>
    match d with
    | node w x y z => node a b c (fs (node w x y z) i)
    | zero =>
      if c = zero then
        if b = zero then
          if a = zero then zero
          else if isSucc a then nest (fun x => node (pred a) x zero zero) zero (i + 1)
          else node (fs a i) zero zero zero
        else if isSucc b then nest (fun x => node a (pred b) x zero) zero (i + 1)
        else node a (fs b i) zero zero
      else if isSucc c then
        if b = zero then
          if a = zero then omegaPowMul (pred c) (i + 1)
          else if isSucc a then
            nest (fun x => node (pred a) x zero zero)
              (addOne (node a zero (pred c) zero)) (i + 1)
          else node (fs a i) (addOne (node a zero (pred c) zero)) zero zero
        else if isSucc b then
          nest (fun x => node a (pred b) x zero) (addOne (node a b (pred c) zero)) (i + 1)
        else node a (fs b i) (addOne (node a b (pred c) zero)) zero
      else node a b (fs c i) zero

theorem fs_zero_eq (i : ℕ) : fs zero i = zero := rfl

theorem fs_cons (a b c w x y z : TNote) (i : ℕ) :
    fs (node a b c (node w x y z)) i = node a b c (fs (node w x y z) i) := rfl

theorem fs_one_eq (i : ℕ) : fs (node zero zero zero zero) i = zero := rfl

theorem fs_phi_zero_zero_succ {a : TNote} (ha : a ≠ zero) (has : isSucc a = true) (i : ℕ) :
    fs (node a zero zero zero) i = nest (fun x => node (pred a) x zero zero) zero (i + 1) := by
  simp [fs, ha, has]

theorem fs_phi_zero_zero_lim {a : TNote} (ha : a ≠ zero) (has : isSucc a = false) (i : ℕ) :
    fs (node a zero zero zero) i = node (fs a i) zero zero zero := by
  simp [fs, ha, has]

theorem fs_phi_zero_succ {a b : TNote} (hb : b ≠ zero) (hbs : isSucc b = true) (i : ℕ) :
    fs (node a b zero zero) i = nest (fun x => node a (pred b) x zero) zero (i + 1) := by
  simp [fs, hb, hbs]

theorem fs_phi_zero_lim {a b : TNote} (hb : b ≠ zero) (hbs : isSucc b = false) (i : ℕ) :
    fs (node a b zero zero) i = node a (fs b i) zero zero := by
  simp [fs, hb, hbs]

theorem fs_omega_succ {c : TNote} (hc : c ≠ zero) (hcs : isSucc c = true) (i : ℕ) :
    fs (node zero zero c zero) i = omegaPowMul (pred c) (i + 1) := by
  simp [fs, hc, hcs]

theorem fs_phi_succ_outer_succ {a c : TNote} (ha : a ≠ zero) (hc : c ≠ zero)
    (has : isSucc a = true) (hcs : isSucc c = true) (i : ℕ) :
    fs (node a zero c zero) i =
      nest (fun x => node (pred a) x zero zero) (addOne (node a zero (pred c) zero)) (i + 1) := by
  simp [fs, ha, hc, has, hcs]

theorem fs_phi_lim_outer_succ {a c : TNote} (ha : a ≠ zero) (hc : c ≠ zero)
    (has : isSucc a = false) (hcs : isSucc c = true) (i : ℕ) :
    fs (node a zero c zero) i =
      node (fs a i) (addOne (node a zero (pred c) zero)) zero zero := by
  simp [fs, ha, hc, has, hcs]

theorem fs_phi_mid_succ_outer_succ {a b c : TNote} (hb : b ≠ zero) (hc : c ≠ zero)
    (hbs : isSucc b = true) (hcs : isSucc c = true) (i : ℕ) :
    fs (node a b c zero) i =
      nest (fun x => node a (pred b) x zero) (addOne (node a b (pred c) zero)) (i + 1) := by
  simp [fs, hb, hc, hbs, hcs]

theorem fs_phi_mid_lim_outer_succ {a b c : TNote} (hb : b ≠ zero) (hc : c ≠ zero)
    (hbs : isSucc b = false) (hcs : isSucc c = true) (i : ℕ) :
    fs (node a b c zero) i = node a (fs b i) (addOne (node a b (pred c) zero)) zero := by
  simp [fs, hb, hc, hbs, hcs]

theorem fs_phi_outer_lim {a b c : TNote} (hc : c ≠ zero) (hcs : isSucc c = false) (i : ℕ) :
    fs (node a b c zero) i = node a b (fs c i) zero := by
  simp [fs, hc, hcs]

theorem fs_value_lt : ∀ (t : TNote), t ≠ zero → ∀ i : ℕ, (fs t i).value < t.value := by
  intro t
  induction t with
  | zero => intro h; exact absurd rfl h
  | node a b c d iha ihb ihc ihd =>
    intro _ i
    cases d with
    | node w x y z =>
      have hd : (fs (node w x y z) i).value < (node w x y z).value := ihd (by simp) i
      rw [fs_cons, value_node, value_node]
      exact add_lt_add_right hd _
    | zero =>
      by_cases hc : c = zero
      · subst hc
        by_cases hb : b = zero
        · subst hb
          by_cases ha : a = zero
          · subst ha
            rw [fs_one_eq, value_zero, value_node, value_zero, add_zero, veblen3_zero,
              veblen_zero_apply, opow_zero]
            exact zero_lt_one
          · by_cases has : isSucc a = true
            · have hval : a.value = (pred a).value + 1 := value_pred has
              have hlt : (pred a).value < a.value := by rw [hval]; exact lt_add_one _
              rw [fs_phi_zero_zero_succ ha has, value_node, value_zero, add_zero]
              refine nest_value_lt (Y := veblen3 a.value 0 0) ?_ (i + 1) (by simpa using
                (veblen3_pos (a := a.value) (b := 0) (c := 0)))
              intro x hx
              simpa using veblen3_lt_of_outer_lt hlt hx
            · rw [Bool.not_eq_true] at has
              rw [fs_phi_zero_zero_lim ha has, value_node, value_node, value_zero, add_zero,
                add_zero]
              exact veblen3_outer_strictMono_zero (iha ha i)
        · by_cases hbs : isSucc b = true
          · have hval : b.value = (pred b).value + 1 := value_pred hbs
            have hlt : (pred b).value < b.value := by rw [hval]; exact lt_add_one _
            rw [fs_phi_zero_succ hb hbs, value_node, value_zero, add_zero]
            refine nest_value_lt (Y := veblen3 a.value b.value 0) ?_ (i + 1) (by simpa using
              (veblen3_pos (a := a.value) (b := b.value) (c := 0)))
            intro x hx
            have : veblen3 a.value (pred b).value x.value <
                veblen3 a.value (pred b).value (veblen3 a.value b.value 0) :=
              veblen3_right_strictMono _ _ hx
            simpa [veblen3_veblen3_of_lt hlt] using this
          · rw [Bool.not_eq_true] at hbs
            rw [fs_phi_zero_lim hb hbs, value_node, value_node, value_zero, add_zero, add_zero]
            exact veblen3_middle_strictMono a.value (ihb hb i)
      · by_cases hcs : isSucc c = true
        · have hcval : c.value = (pred c).value + 1 := value_pred hcs
          have hclt : (pred c).value < c.value := by rw [hcval]; exact lt_add_one _
          by_cases hb : b = zero
          · subst hb
            have hstep : veblen3 a.value 0 (pred c).value + 1 < veblen3 a.value 0 c.value :=
              lt_veblen3_succ (veblen3_right_strictMono _ _ hclt) veblen3_pos
            by_cases ha : a = zero
            · subst ha
              rw [fs_omega_succ hc hcs, value_omegaPowMul, value_node, value_zero, add_zero,
                veblen3_zero, veblen_zero_apply, hcval, opow_add, opow_one]
              refine mul_lt_mul_of_pos_left ?_ (opow_pos _ omega0_pos)
              exact_mod_cast natCast_lt_omega0 (i + 1)
            · by_cases has : isSucc a = true
              · have haval : a.value = (pred a).value + 1 := value_pred has
                have halt : (pred a).value < a.value := by rw [haval]; exact lt_add_one _
                rw [fs_phi_succ_outer_succ ha hc has hcs, value_node, value_zero, add_zero]
                refine nest_value_lt (Y := veblen3 a.value 0 c.value) ?_ (i + 1) ?_
                · intro x hx
                  simpa using veblen3_lt_of_outer_lt halt hx
                · simpa using hstep
              · rw [Bool.not_eq_true] at has
                rw [fs_phi_lim_outer_succ ha hc has hcs, value_node, value_node, value_zero,
                  add_zero, add_zero, value_addOne, value_node, value_zero, add_zero]
                exact veblen3_lt_of_outer_lt (iha ha i) hstep
          · have hstep : veblen3 a.value b.value (pred c).value + 1 <
                veblen3 a.value b.value c.value :=
              lt_veblen3_succ (veblen3_right_strictMono _ _ hclt) veblen3_pos
            by_cases hbs : isSucc b = true
            · have hbval : b.value = (pred b).value + 1 := value_pred hbs
              have hblt : (pred b).value < b.value := by rw [hbval]; exact lt_add_one _
              rw [fs_phi_mid_succ_outer_succ hb hc hbs hcs, value_node, value_zero, add_zero]
              refine nest_value_lt (Y := veblen3 a.value b.value c.value) ?_ (i + 1) ?_
              · intro x hx
                have : veblen3 a.value (pred b).value x.value <
                    veblen3 a.value (pred b).value (veblen3 a.value b.value c.value) :=
                  veblen3_right_strictMono _ _ hx
                simpa [veblen3_veblen3_of_lt hblt] using this
              · simpa using hstep
            · rw [Bool.not_eq_true] at hbs
              rw [fs_phi_mid_lim_outer_succ hb hc hbs hcs, value_node, value_node, value_zero,
                add_zero, add_zero, value_addOne, value_node, value_zero, add_zero]
              exact veblen3_lt_veblen3_middle (ihb hb i) hstep
        · rw [Bool.not_eq_true] at hcs
          rw [fs_phi_outer_lim hc hcs, value_node, value_node, value_zero, add_zero, add_zero]
          exact veblen3_right_strictMono _ _ (ihc hc i)

end TNote

end Contender11


/-!
# The fast-growing hierarchy along the Veblen notations, relativized to a base function

For a base function `g : ℕ → ℕ` we define
```
fgh g t n = g n                        if t denotes 0,
fgh g t n = (fgh g (fs t n))^[n] n     otherwise,
```
where `fs t n` is the fundamental sequence of `Contenders.Contender11.Notation`. The recursion
terminates because `fs t n` denotes a strictly smaller ordinal than `t`. For `t` denoting a
successor ordinal `α + 1` this is the usual clause `f_{α+1}(n) = f_α^[n](n)`, and for `t` denoting
a limit ordinal it is the usual clause `f_α(n) = f_{α[n]}(n)`.
-/

namespace Contender11

open TNote

/-- The fast-growing hierarchy along the Veblen notations `TNote`, relativized to a base
function `g`. -/
def fgh (g : ℕ → ℕ) : TNote → ℕ → ℕ
  | t, n => if _h : t = zero then g n else (fgh g (TNote.fs t n))^[n] n
  termination_by t => t.value
  decreasing_by exact TNote.fs_value_lt t ‹¬ t = zero› n

theorem fgh_zero (g : ℕ → ℕ) (n : ℕ) : fgh g zero n = g n := by
  rw [fgh]; simp

theorem fgh_of_ne_zero (g : ℕ → ℕ) {t : TNote} (h : t ≠ zero) (n : ℕ) :
    fgh g t n = (fgh g (fs t n))^[n] n := by
  rw [fgh]; simp [h]

section Iterate

variable {f : ℕ → ℕ}

theorem one_le_iterate (hf : ∀ m, 1 ≤ m → m ≤ f m) : ∀ (k x : ℕ), 1 ≤ x → 1 ≤ f^[k] x := by
  intro k
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
    intro x hx
    rw [Function.iterate_succ_apply]
    exact ih _ (le_trans hx (hf x hx))

theorem self_le_iterate (hf : ∀ m, 1 ≤ m → m ≤ f m) : ∀ (k x : ℕ), 1 ≤ x → x ≤ f^[k] x := by
  intro k
  induction k with
  | zero => intro x _; simp
  | succ k ih =>
    intro x hx
    rw [Function.iterate_succ_apply]
    exact le_trans (hf x hx) (ih _ (le_trans hx (hf x hx)))

theorem apply_le_iterate (hf : ∀ m, 1 ≤ m → m ≤ f m) {k x : ℕ} (hk : 1 ≤ k) (hx : 1 ≤ x) :
    f x ≤ f^[k] x := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Function.iterate_succ_apply]
  exact self_le_iterate hf k _ (le_trans hx (hf x hx))

end Iterate

variable {g : ℕ → ℕ}

/-- Every function in the hierarchy dominates the base function. -/
theorem base_le_fgh (hinfl : ∀ n, n < g n) :
    ∀ (t : TNote) (n : ℕ), 1 ≤ n → g n ≤ fgh g t n := by
  have key : ∀ o : Ordinal, ∀ t : TNote, t.value = o → ∀ n : ℕ, 1 ≤ n → g n ≤ fgh g t n := by
    intro o
    induction o using WellFoundedLT.induction with
    | _ o ih =>
      intro t ht n hn
      by_cases h : t = zero
      · subst h
        simp [fgh_zero]
      · have hlt : (fs t n).value < o := ht ▸ fs_value_lt t h n
        have ih' : ∀ m : ℕ, 1 ≤ m → g m ≤ fgh g (fs t n) m :=
          ih _ hlt (fs t n) rfl
        have hstep : ∀ m : ℕ, 1 ≤ m → m ≤ fgh g (fs t n) m := fun m hm =>
          le_trans (hinfl m).le (ih' m hm)
        rw [fgh_of_ne_zero g h n]
        exact le_trans (ih' n hn) (apply_le_iterate hstep hn hn)
  intro t n hn
  exact key t.value t rfl n hn

/-- Every function in the hierarchy is inflationary (on positive inputs). -/
theorem lt_fgh (hinfl : ∀ n, n < g n) (t : TNote) (n : ℕ) (hn : 1 ≤ n) : n < fgh g t n :=
  lt_of_lt_of_le (hinfl n) (base_le_fgh hinfl t n hn)

/-- At any nonzero notation, the hierarchy strictly dominates the base function. -/
theorem base_lt_fgh (hmono : StrictMono g) (hinfl : ∀ n, n < g n) {t : TNote} (h : t ≠ zero)
    {n : ℕ} (hn : 2 ≤ n) : g n < fgh g t n := by
  set f := fgh g (fs t n) with hf
  have hstep : ∀ m : ℕ, 1 ≤ m → m ≤ f m := fun m hm => (lt_fgh hinfl (fs t n) m hm).le
  obtain ⟨k, rfl⟩ : ∃ k', n = k' + 1 := ⟨n - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  have hn1 : 1 ≤ k + 1 := by omega
  have hx : k + 1 < f^[k] (k + 1) :=
    lt_of_lt_of_le (lt_fgh hinfl (fs t (k + 1)) (k + 1) hn1) (apply_le_iterate hstep hk hn1)
  rw [fgh_of_ne_zero g h (k + 1), Function.iterate_succ_apply']
  calc g (k + 1) < g (f^[k] (k + 1)) := hmono hx
    _ ≤ f (f^[k] (k + 1)) := base_le_fgh hinfl (fs t (k + 1)) _ (by omega)

end Contender11


/-!
# Contender 11: the fast-growing hierarchy up to the Ackermann ordinal

The first part of this file builds the three-argument Veblen function on ordinals on top of
Mathlib's binary Veblen function. The second part sets up a notation system `TNote` for the
ordinals below the Ackermann ordinal `φ(1,0,0,0)`, built from that three-argument Veblen
function `φ`, together with fundamental sequences `fs`. The third part defines the associated
fast-growing hierarchy `fgh g`, relativized to a base function `g`:
```
fgh g 0 n = g n,   fgh g t n = (fgh g (fs t n))^[n] n  for t ≠ 0.
```

The contender is `f_{A[googol]}(googol)` in this hierarchy, where `googol = 10 ^ 100`, where
`A[k] = φ(φ(⋯φ(0,0,0)⋯,0,0),0,0)` with `k` nested applications is the `k`-th term of the
canonical sequence converging to the Ackermann ordinal `A`, and where the base function is
`n ↦ conwayChain (List.replicate n 100)`. Relativizing to Conway chains costs nothing
mathematically — the growth rate is governed by the Ackermann ordinal, far beyond the `ω²` level
of chained arrows — but it makes the comparison with the previous contender immediate: the base
function alone already reproduces `contender_10` at the input `100`.
-/

namespace Contender11

open TNote

/-- The base function of the hierarchy: `chainBase n` is the Conway chain of `n` hundreds. -/
def chainBase (n : ℕ) : ℕ := conwayChain (List.replicate n 100)

theorem chainBase_lt_succ (n : ℕ) : chainBase n < chainBase (n + 1) := by
  have h := conwayChain_append_lt (List.replicate n 100) [100] (by simp) (by simp) (by simp)
  have hr : (List.replicate n 100).append [100] = List.replicate (n + 1) 100 := by
    simpa using (List.replicate_succ' (n := n) (a := 100)).symm
  rwa [hr] at h

theorem chainBase_strictMono : StrictMono chainBase :=
  strictMono_nat_of_lt_succ chainBase_lt_succ

theorem lt_chainBase (n : ℕ) : n < chainBase n := by
  induction n with
  | zero => simp [chainBase, conwayChain, reverseConwayChain]
  | succ n ih => exact lt_of_le_of_lt ih (chainBase_lt_succ n)

/-- `ackTower k` denotes `φ(φ(⋯φ(0,0,0)⋯,0,0),0,0)` with `k` nested applications of
`φ(·,0,0)`; these are the terms of the canonical sequence converging to the Ackermann ordinal.
Note that `ackTower 2` denotes the Feferman–Schütte ordinal `Γ₀ = φ(1,0,0)`. -/
def ackTower : ℕ → TNote
  | 0 => zero
  | (k + 1) => node (ackTower k) zero zero zero

theorem ackTower_ne_zero {k : ℕ} (h : k ≠ 0) : ackTower k ≠ zero := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp [ackTower]

end Contender11

def contender_11 : Nat :=
  Contender11.fgh Contender11.chainBase (Contender11.ackTower (10 ^ 100)) (10 ^ 100)

theorem contender_10_lt_contender_11 : contender_10 < contender_11 := by
  have h10 : contender_10 = Contender11.chainBase 100 := rfl
  have hmono : StrictMono Contender11.chainBase := Contender11.chainBase_strictMono
  have hinfl : ∀ n, n < Contender11.chainBase n := Contender11.lt_chainBase
  have hbig : Contender11.chainBase 100 < Contender11.chainBase (10 ^ 100) :=
    hmono (by norm_num)
  have hlt : Contender11.chainBase (10 ^ 100) < contender_11 :=
    Contender11.base_lt_fgh hmono hinfl
      (Contender11.ackTower_ne_zero (by positivity)) (by norm_num)
  rw [h10]
  exact hbig.trans hlt
