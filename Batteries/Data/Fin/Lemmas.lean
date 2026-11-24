/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

meta import Batteries.Tactic.Alias

public import Batteries.Data.Fin.Basic

public section

namespace Fin

attribute [norm_cast] val_last

/-! ### order -/

theorem ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b ≠ 0 :=
  Fin.ne_of_gt <| Fin.lt_of_le_of_lt (Fin.zero_le _) hab

theorem ne_last_of_lt {a b : Fin (n + 1)} (hab : a < b) : a ≠ last n :=
  Fin.ne_of_lt <| Fin.lt_of_lt_of_le hab (Fin.le_last _)

/-! ### rev -/

-- Forward port of lean4#11065
attribute [grind =] rev_lt_rev rev_le_rev rev_rev

/-! ### foldl/foldr -/

theorem foldl_assoc {op : α → α → α} [ha : Std.Associative op] {f : Fin n → α} {a₁ a₂} :
    foldl n (fun x i => op x (f i)) (op a₁ a₂) = op a₁ (foldl n (fun x i => op x (f i)) a₂) := by
  induction n generalizing a₂ with
  | zero => simp
  | succ n ih => simp only [foldl_succ, ha.assoc, ih]

theorem foldr_assoc {op : α → α → α} [ha : Std.Associative op] {f : Fin n → α} {a₁ a₂} :
    foldr n (fun i x => op (f i) x) (op a₁ a₂) = op (foldr n (fun i x => op (f i) x) a₁) a₂ := by
  simp only [← Fin.foldl_rev]
  haveI : Std.Associative (flip op) := ⟨fun a b c => (ha.assoc c b a).symm⟩
  exact foldl_assoc (op := flip op)

/-! ### clamp -/

@[simp] theorem coe_clamp (n m : Nat) : (clamp n m : Nat) = min n m := rfl

/-! ### castSucc -/

theorem castSucc_ne_last (i : Fin n) : castSucc i ≠ last n := Fin.ne_of_lt (castSucc_lt_last _)

/-! ### succ, castSucc -/

theorem le_castSucc_iff_lt_succ {i : Fin (n + 1)} {j : Fin n} :
    i ≤ j.castSucc ↔ i < j.succ := le_castSucc_iff

theorem succ_le_or_le_castSucc (i : Fin (n + 1)) (j : Fin n) : j.succ ≤ i ∨ i ≤ j.castSucc :=
  (Fin.lt_or_le _ _).imp_left castSucc_lt_iff_succ_le.mp

theorem castSucc_lt_or_lt_succ (i : Fin (n + 1)) (j : Fin n) : j.castSucc < i ∨ i < j.succ :=
  (Fin.lt_or_le _ _).imp_right le_castSucc_iff_lt_succ.mp

/-! ### castPred -/

@[simp, grind =] theorem val_castPred (i : Fin (n + 1)) (h : i ≠ last n) :
    (castPred i h : Nat) = i := rfl

@[simp] theorem castPred_castSucc (i : Fin n) :
    castPred (castSucc i) (castSucc_ne_last i) = i := rfl

@[simp] theorem castSucc_castPred (i : Fin (n + 1)) (h : i ≠ last n) :
    castSucc (castPred i h) = i := rfl

/-! ### punchOut -/

/-! #### Value and endpoints -/

@[simp, grind =] theorem val_punchOut (p i : Fin (n + 1)) (h : i ≠ p) :
    (punchOut p i h : Nat) = if p.val < i.val then i.val - 1 else i.val := by grind [punchOut]

@[simp] theorem punchOut_zero : punchOut (n := n) 0 = pred :=
  funext fun _ => funext fun h => Fin.ext (ite_eq_left (Nat.pos_of_ne_zero (Fin.val_ne_of_ne h)))

theorem punchOut_zero_apply (i : Fin (n + 1)) (h : i ≠ 0) :
    punchOut 0 i h = pred i h := by simp

@[simp] theorem punchOut_last : punchOut (last n) = castPred :=
  funext fun _ => funext fun h =>
    Fin.ext (ite_eq_right (Nat.not_lt.mpr (Nat.le_of_lt (val_lt_last h))))

theorem punchOut_last_apply (i : Fin (n + 1)) (h : i ≠ last n) :
    punchOut (last n) i h = castPred i h := by simp

/-! #### Case splits -/

theorem punchOut_of_lt {p i : Fin (n + 1)} (hip : i < p) :
    punchOut p i (Fin.ne_of_lt hip) = castPred i (ne_last_of_lt hip) :=
  Fin.ext (ite_eq_right (Nat.lt_asymm hip))

theorem punchOut_of_gt {p i : Fin (n + 1)} (hpi : p < i) :
    punchOut p i (Fin.ne_of_gt hpi) = pred i (ne_zero_of_lt hpi) := Fin.ext (ite_eq_left hpi)

/-! #### Pivot shifts

Not `simp`: the gluing lemmas `punchOut_castSucc` and `punchOut_succ` fire first. -/

theorem punchOut_succ_succ (p i : Fin (n + 1)) (h : i ≠ p) :
    punchOut (succ p) (succ i) (mt succ_inj.mp h) = succ (punchOut p i h) := by grind

theorem punchOut_succ_zero (p : Fin (n + 1)) :
    punchOut (succ p) 0 (succ_ne_zero p).symm = 0 := rfl

theorem punchOut_castSucc_castSucc (p i : Fin (n + 1)) (h : i ≠ p) :
    punchOut (castSucc p) (castSucc i) (mt castSucc_inj.mp h) =
    castSucc (punchOut p i h) := rfl

theorem punchOut_castSucc_last (p : Fin (n + 1)) :
    punchOut (castSucc p) (last (n + 1)) (castSucc_ne_last p).symm = last n :=
  Fin.ext (ite_eq_left p.isLt)

/-! #### Injectivity and order -/

@[simp] theorem punchOut_eq_punchOut_iff {p i j : Fin (n + 1)} {hi : i ≠ p} {hj : j ≠ p} :
    punchOut p i hi = punchOut p j hj ↔ i = j := by grind

@[simp] theorem punchOut_lt_punchOut_iff {p i j : Fin (n + 1)} {hi : i ≠ p} {hj : j ≠ p} :
    punchOut p i hi < punchOut p j hj ↔ i < j := by grind

@[simp] theorem punchOut_le_punchOut_iff {p i j : Fin (n + 1)} {hi : i ≠ p} {hj : j ≠ p} :
    punchOut p i hi ≤ punchOut p j hj ↔ i ≤ j := by grind

/-! ### punchIn -/

/-! #### Value and endpoints -/

@[simp, grind =] theorem val_punchIn (p : Fin (n + 1)) (i : Fin n) :
    (punchIn p i : Nat) = if p.val ≤ i.val then i.val + 1 else i.val := by grind [punchIn]

@[simp] theorem punchIn_zero : punchIn (n := n) 0 = succ := rfl

theorem punchIn_zero_apply (i : Fin n) : punchIn 0 i = succ i := by simp

@[simp] theorem punchIn_last : punchIn (last n) = castSucc :=
  funext fun i => Fin.ext (ite_eq_right (Nat.not_le.mpr i.isLt))

theorem punchIn_last_apply (i : Fin n) : punchIn (last n) i = castSucc i := by simp

/-! #### Missing the pivot -/

theorem punchIn_ne (p : Fin (n + 1)) (i : Fin n) : punchIn p i ≠ p := by grind

theorem ne_iff_exists_punchIn_eq {p i : Fin (n + 1)} : i ≠ p ↔ ∃ j, punchIn p j = i :=
  ⟨fun h => ⟨punchOut p i h, by grind⟩, by grind⟩

/-! #### Case splits -/

theorem punchIn_of_lt {p : Fin (n + 1)} {i : Fin n} (h : i.val < p.val) :
    punchIn p i = castSucc i := Fin.ext (ite_eq_right (Nat.not_le.mpr h))

theorem punchIn_of_le {p : Fin (n + 1)} {i : Fin n} (h : p.val ≤ i.val) :
    punchIn p i = succ i := Fin.ext (ite_eq_left h)

/-! #### Pivot shifts -/

@[simp] theorem punchIn_succ_succ (p : Fin (n + 1)) (i : Fin n) :
    punchIn (succ p) (succ i) = succ (punchIn p i) := by grind

@[simp] theorem punchIn_succ_zero (p : Fin (n + 1)) : punchIn (succ p) 0 = 0 := rfl

@[simp] theorem punchIn_castSucc_castSucc (p : Fin (n + 1)) (i : Fin n) :
    punchIn (castSucc p) (castSucc i) = castSucc (punchIn p i) := rfl

@[simp] theorem punchIn_castSucc_last (p : Fin (n + 1)) :
    punchIn (castSucc p) (last n) = last (n + 1) := Fin.ext (ite_eq_left (Nat.le_of_lt_succ p.isLt))

/-! #### Injectivity and order -/

@[simp] theorem punchIn_eq_punchIn_iff {p : Fin (n + 1)} {i j : Fin n} :
    punchIn p i = punchIn p j ↔ i = j := by grind

@[simp] theorem punchIn_lt_punchIn_iff {p : Fin (n + 1)} {i j : Fin n} :
    punchIn p i < punchIn p j ↔ i < j := by grind

@[simp] theorem punchIn_le_punchIn_iff {p : Fin (n + 1)} {i j : Fin n} :
    punchIn p i ≤ punchIn p j ↔ i ≤ j := by grind

/-! #### Comparison with the pivot -/

theorem punchIn_lt_iff {p : Fin (n + 1)} {i : Fin n} :
    punchIn p i < p ↔ i.val < p.val := by grind

theorem punchIn_le_iff {p : Fin (n + 1)} {i : Fin n} :
    punchIn p i ≤ p ↔ i.val < p.val := by grind

theorem lt_punchIn_iff {p : Fin (n + 1)} {i : Fin n} :
    p < punchIn p i ↔ p.val ≤ i.val := by grind

theorem le_punchIn_iff {p : Fin (n + 1)} {i : Fin n} :
    p ≤ punchIn p i ↔ p.val ≤ i.val := by grind

/-! ### pinch -/

/-! #### Value -/

@[simp, grind =] theorem val_pinch (p : Fin n) (i : Fin (n + 1)) :
    (pinch p i : Nat) = if p.val < i.val then i.val - 1 else i.val := by grind [pinch]

/-! #### Case splits and endpoints -/

theorem pinch_of_le {p : Fin n} {i : Fin (n + 1)} (h : i.val ≤ p.val) :
    pinch p i = castPred i (ne_last_of_lt (b := succ p) (Nat.lt_succ_of_le h)) :=
  Fin.ext (ite_eq_right (Nat.not_lt.mpr h))

theorem pinch_of_lt {p : Fin n} {i : Fin (n + 1)} (h : p.val < i.val) :
    pinch p i = pred i (ne_zero_of_lt (a := castSucc p) h) := Fin.ext (ite_eq_left h)

theorem pred_eq_pinch_zero [NeZero n] (i : Fin (n + 1)) (h : i ≠ 0) :
    pred i h = pinch 0 i := Fin.ext (ite_eq_left (Nat.pos_of_ne_zero (Fin.val_ne_of_ne h))).symm

theorem castPred_eq_pinch_last (i : Fin (n + 2)) (h : i ≠ last (n + 1)) :
    castPred i h = pinch (last n) i :=
  Fin.ext (ite_eq_right (Nat.not_lt.mpr (Nat.le_of_lt_succ (val_lt_last h)))).symm

/-! #### Pivot shifts -/

@[simp] theorem pinch_succ_succ (p : Fin n) (i : Fin (n + 1)) :
    pinch (succ p) (succ i) = succ (pinch p i) := by grind

@[simp] theorem pinch_succ_zero (p : Fin n) : pinch (succ p) 0 = 0 := rfl

@[simp] theorem pinch_castSucc_castSucc (p : Fin n) (i : Fin (n + 1)) :
    pinch (castSucc p) (castSucc i) = castSucc (pinch p i) := rfl

@[simp] theorem pinch_castSucc_last (p : Fin n) :
    pinch (castSucc p) (last (n + 1)) = last n := Fin.ext (ite_eq_left (Nat.lt_succ_of_lt p.isLt))

/-! #### Collapse -/

@[simp] theorem pinch_castSucc_self (p : Fin n) : pinch p p.castSucc = p :=
  Fin.ext (ite_eq_right (Nat.lt_irrefl _))
@[simp] theorem pinch_succ_self (p : Fin n) : pinch p p.succ = p :=
  Fin.ext (ite_eq_left (Nat.lt_succ_self _))

/-! #### Surjectivity, fibres and order -/

theorem exists_pinch_eq (p : Fin n) (j : Fin n) : ∃ i, pinch p i = j :=
  ⟨(punchIn (castSucc p) j), by grind⟩

theorem pinch_eq_pinch_iff {p : Fin n} {i j : Fin (n + 1)} :
    pinch p i = pinch p j ↔
      i = j ∨ i = castSucc p ∧ j = succ p ∨ i = succ p ∧ j = castSucc p := by grind

theorem pinch_le_pinch {p : Fin n} {i j : Fin (n + 1)} :
    i ≤ j → pinch p i ≤ pinch p j := by grind

theorem lt_of_pinch_lt_pinch {p : Fin n} {i j : Fin (n + 1)} :
     pinch p i < pinch p j → i < j := by grind

/-! ### punchIn / punchOut -/

@[simp] theorem punchOut_punchIn_right (p : Fin (n + 1)) (i : Fin n) :
    punchOut p (punchIn p i) (punchIn_ne p i) = i := by grind

@[simp] theorem punchIn_punchOut (p i : Fin (n + 1)) (h : i ≠ p) :
    punchIn p (punchOut p i h) = i := by grind

/-! ### punchIn / punchOut / pinch interactions -/

/-! #### Gluing: `punchOut` at a neighbour of the gap is `pinch` -/

@[simp] theorem punchOut_punchIn_left (p : Fin n) (i : Fin (n + 1)) :
    punchOut (punchIn i p) i (punchIn_ne i p).symm = pinch p i := by grind

@[simp] theorem punchOut_castSucc (p : Fin n) (i : Fin (n + 1)) (h : i ≠ castSucc p) :
    punchOut (castSucc p) i h = pinch p i := by grind

@[simp] theorem punchOut_succ (p : Fin n) (i : Fin (n + 1)) (h : i ≠ succ p) :
    punchOut (succ p) i h = pinch p i := by grind

/-! #### Sections of `pinch` -/

@[simp] theorem pinch_punchIn_castSucc (p j : Fin n) :
    pinch p (punchIn (castSucc p) j) = j :=
  (punchOut_castSucc p _ (punchIn_ne _ j)).symm.trans (punchOut_punchIn_right _ j)

@[simp] theorem pinch_punchIn_succ (p j : Fin n) :
    pinch p (punchIn (succ p) j) = j :=
  (punchOut_succ p _ (punchIn_ne _ j)).symm.trans (punchOut_punchIn_right _ j)

/-! #### Simplicial identities -/

theorem punchIn_succ_punchIn {i j : Fin (n + 1)} (hij : i ≤ j) (k : Fin n) :
    punchIn (succ j) (punchIn i k) = punchIn (castSucc i) (punchIn j k) := by grind

theorem pinch_pinch_castSucc {i j : Fin n} (hij : i ≤ j) (k : Fin (n + 2)) :
    pinch j (pinch (castSucc i) k) = pinch i (pinch (succ j) k) := by grind

theorem pinch_succ_punchIn_castSucc {i : Fin (n + 1)} {j : Fin n} (hij : i.val ≤ j.val) (k) :
    pinch (succ j) (punchIn (castSucc i) k) = punchIn i (pinch j k) := by grind

theorem pinch_castSucc_punchIn_succ {i : Fin (n + 1)} {j : Fin n} (hji : j.val < i.val) (k) :
    pinch (castSucc j) (punchIn (succ i) k) = punchIn i (pinch j k) := by grind

/-! #### Pairs of distinct positions -/

/-- `pinch i j` is the position of `j` once `punchIn j i` is removed, so punching that gap
back in recovers `j`. -/
@[simp] theorem punchIn_punchIn_pinch (j : Fin (n + 1)) (i : Fin n) :
    punchIn (punchIn j i) (pinch i j) = j := by grind

/-- Describing the two distinct positions `j` and `punchIn j i` from the other one, as
`punchIn j i` and `pinch i j`, and then back again recovers `i`. -/
@[simp] theorem pinch_pinch_punchIn (j : Fin (n + 1)) (i : Fin n) :
    pinch (pinch i j) (punchIn j i) = i := by grind

/-- Removing the two distinct positions `j` and `punchIn j i` leaves the same positions
whichever of them is removed first. -/
@[simp] theorem punchIn_punchIn_punchIn_pinch (j : Fin (n + 2)) (i : Fin (n + 1)) (k) :
    punchIn (punchIn j i) (punchIn (pinch i j) k) = punchIn j (punchIn i k) := by grind

/-! ### sum -/

@[simp, grind =]
theorem sum_zero [Zero α] [Add α] (x : Fin 0 → α) :
    Fin.sum x = 0 := by
  simp [Fin.sum]

theorem sum_succ [Zero α] [Add α] (x : Fin (n + 1) → α) :
    Fin.sum x = x 0 + Fin.sum (x ·.succ) := by
  simp [Fin.sum, foldr_succ]

@[simp, grind =]
theorem sum_eq_sum_map_finRange [Zero α] [Add α] (x : Fin n → α) :
    Fin.sum x = (List.finRange n |>.map x).sum := by
  simp only [Fin.sum, foldr_eq_finRange_foldr, List.sum, List.foldr_map]

/-! ### prod -/

@[simp, grind =]
theorem prod_zero [One α] [Mul α] (x : Fin 0 → α) :
    Fin.prod x = 1 := by
  simp [Fin.prod]

theorem prod_succ [One α] [Mul α] (x : Fin (n + 1) → α) :
    Fin.prod x = x 0 * Fin.prod (x ·.succ) := by
  simp [Fin.prod, foldr_succ]

@[simp, grind =]
theorem prod_eq_prod_map_finRange [One α] [Mul α] (x : Fin n → α) :
    Fin.prod x = (List.finRange n |>.map x).prod := by
  simp only [Fin.prod, foldr_eq_finRange_foldr, List.prod, List.foldr_map]

/-! ### countP -/

@[simp, grind =] theorem countP_zero (p : Fin 0 → Bool) : Fin.countP p = 0 := by
  simp [Fin.countP]

@[simp, grind =] theorem countP_one (p : Fin 1 → Bool) : Fin.countP p = (p 0).toNat := by
  simp [Fin.countP, List.finRange_succ]

theorem countP_succ (p : Fin (n + 1) → Bool) :
    Fin.countP p = (p 0).toNat + Fin.countP (p ·.succ) := by
  simp [Fin.countP, List.finRange_succ]; rfl

@[simp, grind =]
theorem countP_eq_countP_map_finRange (x : Fin n → Bool) :
    Fin.countP x = (List.finRange n).countP x := by
  induction n with
  | zero => rfl
  | succ n ih => simp +arith [countP_succ, List.finRange_succ, List.countP_cons, List.countP_map,
      Bool.cond_eq_ite, Bool.toNat, ih]; rfl

@[grind .]
theorem countP_le (p : Fin n → Bool) : Fin.countP p ≤ n := by
  induction n with simp only [countP_zero, countP_succ, Nat.le_refl]
  | succ _ ih =>
    rw [Nat.add_comm]
    apply Nat.add_le_add
    · exact ih ..
    · exact Bool.toNat_le ..

/-! ### findSome? -/

@[simp] theorem findSome?_zero {f : Fin 0 → Option α} : findSome? f = none := by simp [findSome?]

@[simp] theorem findSome?_one {f : Fin 1 → Option α} : findSome? f = f 0 := by
  simp [findSome?, foldl_succ]

theorem findSome?_succ {f : Fin (n+1) → Option α} :
    findSome? f = (f 0).or (findSome? (f ·.succ)) := by
  simp only [findSome?, foldl_succ, Option.orElse_eq_orElse, Option.orElse_eq_or]
  exact Eq.trans (by cases (f 0) <;> rfl) foldl_assoc

theorem findSome?_succ_of_some {f : Fin (n+1) → Option α} (h : f 0 = some x) :
    findSome? f = some x := findSome?_succ.trans (h ▸ Option.some_or)

theorem findSome?_succ_of_isSome {f : Fin (n+1) → Option α} (h : (f 0).isSome) :
    findSome? f = f 0 := findSome?_succ.trans (Option.or_of_isSome h)

theorem findSome?_succ_of_none {f : Fin (n+1) → Option α} (h : f 0 = none) :
    findSome? f = findSome? (f ·.succ) := findSome?_succ.trans (Option.or_eq_right_of_none h)

theorem findSome?_succ_of_isNone {f : Fin (n+1) → Option α} (h : (f 0).isNone) :
    findSome? f = findSome? (f ·.succ) := findSome?_succ.trans (Option.or_of_isNone h)

@[simp, grind =]
theorem findSome?_eq_some_iff {f : Fin n → Option α} :
    findSome? f = some a ↔ ∃ i, f i = some a ∧ ∀ j < i, f j = none := by
  induction n with
  | zero =>
    simp only [findSome?_zero, reduceCtorEq, forall_fin_zero, and_true, exists_fin_zero]
  | succ n ih =>
    simp only [findSome?_succ, Option.or_eq_some_iff, exists_fin_succ, forall_fin_succ,
      succ_lt_succ_iff, succ_pos, not_lt_zero, ih]
    grind

@[simp, grind =] theorem findSome?_eq_none_iff {f : Fin n → Option α} :
    findSome? f = none ↔ ∀ i, f i = none := by
  induction n with
  | zero => simp only [findSome?_zero, forall_fin_zero]
  | succ n ih => simp only [findSome?_succ, Option.or_eq_none_iff, ih, forall_fin_succ]

theorem isNone_findSome?_iff {f : Fin n → Option α} :
    (findSome? f).isNone ↔ ∀ i, (f i).isNone := by simp

@[simp] theorem isSome_findSome?_iff {f : Fin n → Option α} :
    (findSome? f).isSome ↔ ∃ i, (f i).isSome := by
  cases h : findSome? f <;> grind

theorem exists_minimal_of_findSome?_eq_some {f : Fin n → Option α}
    (h : findSome? f = some x) : ∃ i, f i = some x ∧ ∀ j < i, f j = none :=
  findSome?_eq_some_iff.1 h

theorem exists_eq_some_of_findSome?_eq_some {f : Fin n → Option α}
    (h : findSome? f = some x) : ∃ i, f i = some x := by grind

theorem eq_none_of_findSome?_eq_none {f : Fin n → Option α} (h : findSome? f = none) (i) :
    f i = none := findSome?_eq_none_iff.1 h i

theorem exists_isSome_of_isSome_findSome? {f : Fin n → Option α} (h : (findSome? f).isSome) :
    ∃ i, (f i).isSome := isSome_findSome?_iff.1 h

theorem isNone_of_isNone_findSome? {f : Fin n → Option α} (h : (findSome? f).isNone) :
    (f i).isNone := isNone_findSome?_iff.1 h i

theorem isSome_findSome?_of_isSome {f : Fin n → Option α} (h : (f i).isSome) :
    (findSome? f).isSome := isSome_findSome?_iff.2 ⟨_, h⟩

theorem map_findSome? (f : Fin n → Option α) (g : α → β) :
    (findSome? f).map g = findSome? (Option.map g <| f ·) := by
  induction n with
  | zero => simp
  | succ n ih => simp [findSome?_succ, Option.map_or, ih]

theorem findSome?_guard {p : Fin n → Bool} : findSome? (Option.guard p) = find? p := rfl

theorem bind_findSome?_guard_isSome {f : Fin n → Option α} :
    (findSome? (Option.guard fun i => (f i).isSome)).bind f = findSome? f := by

  cases hf : findSome? f with
  | none => grind
  | some x =>
    simp only [Option.bind_eq_some_iff, findSome?_eq_some_iff, Option.guard_eq_some_iff]
    grind

theorem findSome?_eq_findSome?_finRange (f : Fin n → Option α) :
    findSome? f = (List.finRange n).findSome? f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [findSome?_succ, List.finRange_succ, List.findSome?_cons]
    cases f 0 <;> simp [ih, List.findSome?_map, Function.comp_def]

/-! ### findSomeRev? -/

@[simp]
theorem findSome?_rev {f : Fin n → Option α} : findSome? (f ·.rev) = findSomeRev? f := rfl

@[simp]
theorem findSomeRev?_rev {f : Fin n → Option α} :
    findSomeRev? (f ·.rev) = findSome? f := by simp only [findSomeRev?, rev_rev]

@[simp] theorem findSomeRev?_zero {f : Fin 0 → Option α} : findSomeRev? f = none := by
  simp [findSomeRev?]

@[simp] theorem findSomeRev?_one {f : Fin 1 → Option α} : findSomeRev? f = f 0 := by
  simp [findSomeRev?]

theorem findSomeRev?_succ {f : Fin (n+1) → Option α} :
    findSomeRev? f = (f (last n)).or (findSomeRev? fun i => f i.castSucc) := by
  unfold findSomeRev?
  simp only [findSome?_succ, rev_succ, rev_zero]

@[simp, grind =]
theorem findSomeRev?_eq_some_iff {f : Fin n → Option α} :
    findSomeRev? f = some a ↔ ∃ i, f i = some a ∧ ∀ j, i < j → f j = none :=
  findSome?_eq_some_iff.trans <| ⟨fun ⟨i, h⟩ => ⟨i.rev, by grind,
    fun j hj => have := h.2 j.rev; by grind⟩, fun ⟨i, _⟩ => ⟨i.rev, by grind⟩⟩

@[simp, grind =] theorem findSomeRev?_eq_none_iff {f : Fin n → Option α} :
    findSomeRev? f = none ↔ ∀ i, f i = none :=
  findSome?_eq_none_iff.trans <| ⟨fun h i => have := h i.rev; by grind, by grind⟩

theorem isNone_findSomeRev?_iff {f : Fin n → Option α} :
    (findSomeRev? f).isNone ↔ ∀ i, (f i).isNone := by simp

@[simp] theorem isSome_findSomeRev?_iff {f : Fin n → Option α} :
    (findSomeRev? f).isSome ↔ ∃ i, (f i).isSome := by
  cases h : findSomeRev? f <;> grind

theorem exists_minimal_of_findSomeRev?_eq_some {f : Fin n → Option α}
    (h : findSomeRev? f = some x) : ∃ i, f i = some x ∧ ∀ j, i < j → f j = none :=
  findSomeRev?_eq_some_iff.1 h

theorem exists_eq_some_of_findSomeRev?_eq_some {f : Fin n → Option α}
    (h : findSomeRev? f = some x) : ∃ i, f i = some x := by grind

theorem eq_none_of_findSomeRev?_eq_none {f : Fin n → Option α} (h : findSomeRev? f = none) (i) :
    f i = none := findSomeRev?_eq_none_iff.1 h i

theorem exists_isSome_of_isSome_findSomeRev? {f : Fin n → Option α} (h : (findSomeRev? f).isSome) :
    ∃ i, (f i).isSome := isSome_findSomeRev?_iff.1 h

theorem isNone_of_isNone_findSomeRev? {f : Fin n → Option α} (h : (findSomeRev? f).isNone) :
    (f i).isNone := isNone_findSomeRev?_iff.1 h i

theorem isSome_findSomeRev?_of_isSome {f : Fin n → Option α} (h : (f i).isSome) :
    (findSomeRev? f).isSome := isSome_findSomeRev?_iff.2 ⟨_, h⟩

theorem map_findSomeRev? (f : Fin n → Option α) (g : α → β) :
    (findSomeRev? f).map g = findSomeRev? (Option.map g <| f ·) := by
  induction n with
  | zero => grind [findSomeRev?_zero]
  | succ n ih => grind [findSomeRev?_succ]

@[grind =_]
theorem findSomeRev?_guard {p : Fin n → Bool} : findSomeRev? (Option.guard p) = findRev? p := rfl

theorem bind_findSomeRev?_guard_isSome {f : Fin n → Option α} :
    (findSomeRev? (Option.guard fun i => (f i).isSome)).bind f = findSomeRev? f := by
  cases hf : findSomeRev? f with
  | none => grind
  | some x =>
    simp only [Option.bind_eq_some_iff, findSomeRev?_eq_some_iff, Option.guard_eq_some_iff]
    grind

/-! ### find? -/

theorem find?_zero {p : Fin 0 → Bool} : find? p = none := by simp

theorem find?_one {p : Fin 1 → Bool} : find? p = if p 0 then some 0 else none := by
  simp [Option.guard]

theorem find?_succ {p : Fin (n+1) → Bool} :
    find? p = if p 0 then some 0 else (find? (p ·.succ)).map Fin.succ := by
  simp only [findSome?_succ, Option.guard, fun a => apply_ite (Option.or · a),
    Option.some_or, Option.none_or, map_findSome?, Option.map_ite]

@[grind =]
theorem find?_eq_some_iff {p : Fin n → Bool} :
    find? p = some i ↔ p i ∧ ∀ j, j < i → p j = false := by simp [and_assoc]

theorem isSome_find?_iff {p : Fin n → Bool} :
    (find? p).isSome ↔ ∃ i, p i := by simp

@[grind =]
theorem find?_eq_none_iff {p : Fin n → Bool} : find? p = none ↔ ∀ i, p i = false := by simp

theorem isNone_find?_iff {p : Fin n → Bool} : (find? p).isNone ↔ ∀ i, p i = false := by simp

theorem eq_true_of_find?_eq_some {p : Fin n → Bool} (h : find? p = some i) : p i :=
    (find?_eq_some_iff.mp h).1

theorem eq_false_of_find?_eq_some_of_lt {p : Fin n → Bool} (h : find? p = some i) :
    ∀ j < i, p j = false := (find?_eq_some_iff.mp h).2

theorem eq_false_of_find?_eq_none {p : Fin n → Bool} (h : find? p = none) (i) :
    p i = false := find?_eq_none_iff.1 h i

theorem exists_eq_true_of_isSome_find? {p : Fin n → Bool} (h : (find? p).isSome) :
    ∃ i, p i := isSome_find?_iff.1 h

theorem eq_false_of_isNone_find? {p : Fin n → Bool} (h : (find? p).isNone) : p i = false :=
  isNone_find?_iff.1 h i

theorem isSome_find?_of_eq_true {p : Fin n → Bool} (h : p i) :
    (find? p).isSome := isSome_find?_iff.2 ⟨_, h⟩

theorem get_find?_eq_true {p : Fin n → Bool} (h : (find? p).isSome) : p ((find? p).get h) :=
  eq_true_of_find?_eq_some (Option.some_get _).symm

theorem get_find?_minimal {p : Fin n → Bool} (h : (find? p).isSome) :
    ∀ j, j < (find? p).get h → p j = false :=
  eq_false_of_find?_eq_some_of_lt (Option.some_get _).symm

theorem bind_find?_isSome {f : Fin n → Option α} :
    (find? (fun i => (f i).isSome)).bind f = findSome? f := bind_findSome?_guard_isSome

theorem find?_eq_find?_finRange {p : Fin n → Bool} : find? p = (List.finRange n).find? p :=
  (findSome?_eq_findSome?_finRange _).trans (List.findSome?_guard)

theorem exists_eq_true_iff_exists_minimal_eq_true (p : Fin n → Bool):
    (∃ i, p i) ↔ ∃ i, p i ∧ ∀ j < i, p j = false := by cases h : find? p <;> grind

theorem exists_iff_exists_minimal (p : Fin n → Prop) [DecidablePred p] :
    (∃ i, p i) ↔ ∃ i, p i ∧ ∀ j < i, ¬ p j := by cases h : find? (p ·) <;> grind

theorem find?_rev {p : Fin n → Bool} : find? (p ·.rev) = (findRev? p).map rev := by
  simp [← findSomeRev?_rev, map_findSomeRev?, Option.guard_eq_ite]

theorem map_rev_findRev? {p : Fin n → Bool} : (findRev? (p ·.rev)).map rev = find? p := by
  simp only [← find?_rev, rev_rev]

/-! ### findRev? -/

theorem findRev?_zero {p : Fin 0 → Bool} : findRev? p = none := by grind

theorem findRev?_succ {p : Fin (n+1) → Bool} :
    findRev? p = if p (last n) then some (last n)
    else (findRev? fun i => p i.castSucc).map Fin.castSucc := by
  simp only [findSomeRev?_succ, Option.guard, fun a => apply_ite (Option.or · a),
    Option.some_or, Option.none_or, map_findSomeRev?, Option.map_ite]

theorem findRev?_one {p : Fin 1 → Bool} : findRev? p = if p 0 then some 0 else none := by
  grind [findRev?_succ]

@[grind =]
theorem findRev?_eq_some_iff {p : Fin n → Bool} :
    findRev? p = some i ↔ p i ∧ ∀ j, i < j → p j = false := by simp [and_assoc]

@[grind =]
theorem findRev?_eq_none_iff {p : Fin n → Bool} : findRev? p = none ↔ ∀ i, p i = false := by simp

theorem isSome_findRev?_iff {p : Fin n → Bool} :
    (findRev? p).isSome ↔ ∃ i, p i := by simp

theorem isNone_findRev?_iff {p : Fin n → Bool} : (findRev? p).isNone ↔ ∀ i, p i = false := by simp

theorem eq_true_of_findRev?_eq_some {p : Fin n → Bool} (h : findRev? p = some i) : p i :=
    (findRev?_eq_some_iff.mp h).1

theorem eq_false_of_findRev?_eq_some_of_lt {p : Fin n → Bool} (h : findRev? p = some i) :
    ∀ j, i < j → p j = false := (findRev?_eq_some_iff.mp h).2

theorem eq_false_of_findRev?_eq_none {p : Fin n → Bool} (h : findRev? p = none) (i) :
    p i = false := findRev?_eq_none_iff.1 h i

theorem exists_eq_true_of_isSome_findRev? {p : Fin n → Bool} (h : (findRev? p).isSome) :
    ∃ i, p i := isSome_findRev?_iff.1 h

theorem eq_false_of_isNone_findRev? {p : Fin n → Bool} (h : (findRev? p).isNone) : p i = false :=
  isNone_findRev?_iff.1 h i

theorem isSome_findRev?_of_eq_true {p : Fin n → Bool} (h : p i) :
    (findRev? p).isSome := isSome_findRev?_iff.2 ⟨_, h⟩

theorem get_findRev?_eq_true {p : Fin n → Bool} (h : (findRev? p).isSome) :
    p ((findRev? p).get h) := eq_true_of_findRev?_eq_some (Option.some_get _).symm

theorem get_findRev?_maximal {p : Fin n → Bool} (h : (findRev? p).isSome) :
    ∀ j, (findRev? p).get h < j → p j = false :=
  eq_false_of_findRev?_eq_some_of_lt (Option.some_get _).symm

theorem exists_eq_true_iff_exists_maximal_eq_true (p : Fin n → Bool):
    (∃ i, p i) ↔ ∃ i, p i ∧ ∀ j , i < j → p j = false := by cases h : findRev? p <;> grind

theorem exists_iff_exists_maximal (p : Fin n → Prop) [DecidablePred p] :
    (∃ i, p i) ↔ ∃ i, p i ∧ ∀ j, i < j → ¬ p j := by cases h : findRev? (p ·) <;> grind

theorem bind_findRev?_isSome {f : Fin n → Option α} :
    (findRev? (fun i => (f i).isSome)).bind f = findSomeRev? f := bind_findSomeRev?_guard_isSome

theorem findRev?_rev {p : Fin n → Bool} : findRev? (p ·.rev) = (find? p).map rev := by
  simp [← findSome?_rev, map_findSome?, Option.guard_eq_ite]

theorem map_rev_find? {p : Fin n → Bool} : (find? (p ·.rev)).map rev = findRev? p := by
  simp only [← findRev?_rev, rev_rev]

theorem find?_le_findRev? {p : Fin n → Bool} : find? p ≤ findRev? p := by
  cases hl : find? p <;> cases hu : findRev? p <;> grind

theorem find?_eq_findRev?_iff {p : Fin n → Bool} : find? p = findRev? p ↔
    ∀ i j, p i = true → p j = true → i = j := by
  cases h : findRev? p <;> grind

/-! ### divNat / modNat / mkDivMod -/

@[simp, grind =] theorem coe_divNat (i : Fin (m * n)) : (i.divNat : Nat) = i / n := rfl

@[simp, grind =] theorem coe_modNat (i : Fin (m * n)) : (i.modNat : Nat) = i % n := rfl

@[simp, grind =] theorem coe_mkDivMod (i : Fin m) (j : Fin n) :
    (mkDivMod i j : Nat) = i.val.mkDivMod j := rfl

theorem ext_divNat_modNat {a b : Fin (m * n)} (h0 : a.divNat = b.divNat)
    (h1 : a.modNat = b.modNat) : a = b :=
  Fin.ext <| Nat.ext_div_mod (congrArg val h0) (congrArg val h1)

theorem ext_divNat_modNat_iff {a b : Fin (m * n)} :
    a = b ↔ a.divNat = b.divNat ∧ a.modNat = b.modNat := by
  simp [Fin.ext_iff, n.ext_div_mod_iff a]

theorem lt_divNat_modNat_iff {a b : Fin (m * n)} :
    a < b ↔ a.divNat < b.divNat ∨ a.divNat = b.divNat ∧ a.modNat < b.modNat := by
  simp [Fin.lt_def, Fin.ext_iff, n.lt_div_mod_iff a]

theorem le_divNat_modNat_iff {a b : Fin (m * n)} :
    a ≤ b ↔ a.divNat < b.divNat ∨ a.divNat = b.divNat ∧ a.modNat ≤ b.modNat := by
  simp [Fin.lt_def, Fin.le_def, Fin.ext_iff, n.le_div_mod_iff a]

@[simp, grind =] theorem divNat_mkDivMod (i : Fin m) (j : Fin n) : (mkDivMod i j).divNat = i :=
  Fin.ext <| Nat.div_mkDivMod _ _

@[simp, grind =] theorem modNat_mkDivMod (i : Fin m) (j : Fin n) : (mkDivMod i j).modNat = j :=
  Fin.ext <| Nat.mod_mkDivMod _ _

@[simp, grind =] theorem mkDivMod_divNat_modNat (k : Fin (m * n)) :
    k.divNat.mkDivMod k.modNat = k :=
  ext_divNat_modNat (divNat_mkDivMod ..) (modNat_mkDivMod ..)

@[deprecated (since := "2026-11-19")] alias divNat_mkDivMod_modNat := mkDivMod_divNat_modNat

@[simp] theorem mkDivMod_inj {i₁ i₂ : Fin m} {j₁ j₂ : Fin n} :
    mkDivMod i₁ j₁ = mkDivMod i₂ j₂ ↔ i₁ = i₂ ∧ j₁ = j₂ := by
  simp [ext_divNat_modNat_iff]

@[simp] theorem mkDivMod_lt_mkDivMod_iff {i₁ i₂ : Fin m} {j₁ j₂ : Fin n} :
    mkDivMod i₁ j₁ < mkDivMod i₂ j₂ ↔ i₁ < i₂ ∨ i₁ = i₂ ∧ j₁ < j₂ := by
  simp [lt_divNat_modNat_iff]

@[simp] theorem mkDivMod_le_mkDivMod_iff {i₁ i₂ : Fin m} {j₁ j₂ : Fin n} :
    mkDivMod i₁ j₁ ≤ mkDivMod i₂ j₂ ↔ i₁ < i₂ ∨ i₁ = i₂ ∧ j₁ ≤ j₂ := by
  simp [le_divNat_modNat_iff]
