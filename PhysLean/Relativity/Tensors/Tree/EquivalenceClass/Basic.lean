/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.Tree.Basic
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.Basic
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.PermProd
/-!

## Equivalence class on Tensor Trees

This file contains the basic node identities for tensor trees.
More complicated identities appear in there own files.

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open PhysLean.Fin
open TensorProduct

namespace TensorTree

variable {k : Type} [CommRing k] {S : TensorSpecies k}

/-- The relation `tensorRel` on `TensorTree S c` is defined such that `tensorRel t1 t2` is true
  if `t1` and `t2` have the same underlying tensors. -/
def tensorRel {n} {c : Fin n → S.C} (t1 t2 : TensorTree S c) : Prop := t1.tensor = t2.tensor

lemma tensorRel_refl {n} {c : Fin n → S.C} (t : TensorTree S c) : tensorRel t t := rfl

lemma tensorRel_symm {n} {c : Fin n → S.C} {t1 t2 : TensorTree S c} :
    tensorRel t1 t2 → tensorRel t2 t1 :=
  Eq.symm

lemma tensorRel_trans {n} {c : Fin n → S.C} {t1 t2 t3 : TensorTree S c} :
    tensorRel t1 t2 → tensorRel t2 t3 → tensorRel t1 t3 := Eq.trans

lemma tensorRel_equivalence {n} (c : Fin n → S.C) :
    Equivalence (tensorRel (c := c) (S := S)) :=
  { refl := tensorRel_refl,
    symm := tensorRel_symm,
    trans := tensorRel_trans}

instance tensorTreeSetoid {n} (c : Fin n → S.C) : Setoid (TensorTree S c) :=
  Setoid.mk (tensorRel (c := c) (S := S)) (tensorRel_equivalence c)

/-- The equivalence classes of `TensorTree` under the relation `tensorRel`. -/
def _root_.TensorSpecies.TensorTreeQuot (S : TensorSpecies k) {n} (c : Fin n → S.C) : Type :=
    Quot (tensorRel (c := c))

namespace TensorTreeQuot

/-- The projection from `TensorTree` down to `TensorTreeQuot`. -/
def ι {n} {c : Fin n → S.C} (t : TensorTree S c) : S.TensorTreeQuot c := Quot.mk _ t

lemma ι_surjective {n} {c : Fin n → S.C} : Function.Surjective (ι (c := c)) := by
  simp only [Function.Surjective]
  exact fun b => Quotient.exists_rep b

lemma ι_apply_eq_iff_tensorRel {n} {c : Fin n → S.C} {t1 t2 : TensorTree S c} :
    ι t1 = ι t2 ↔ tensorRel t1 t2 := by
  simp only [ι]
  rw [Equivalence.quot_mk_eq_iff (tensorRel_equivalence c)]

lemma ι_apply_eq_iff_tensor_apply_eq {n} {c : Fin n → S.C} {t1 t2 : TensorTree S c} :
    ι t1 = ι t2 ↔ t1.tensor = t2.tensor := by
  rw [ι_apply_eq_iff_tensorRel]
  simp [tensorRel]

/-!

## Addition and smul

-/

/-- The addition of two equivalence classes of tensor trees. -/
def addQuot {n} {c : Fin n → S.C} :
    S.TensorTreeQuot c → S.TensorTreeQuot c → S.TensorTreeQuot c := by
  refine Quot.lift₂ (fun t1 t2 => ι (t1.add t2)) ?_ ?_
  · intro t1 t2  t3 h1
    simp only [tensorRel] at h1
    simp only
    rw [ι_apply_eq_iff_tensor_apply_eq]
    rw [add_tensor, add_tensor, h1]
  · intro t1 t2 t3 h1
    simp only [tensorRel] at h1
    simp only
    rw [ι_apply_eq_iff_tensor_apply_eq]
    rw [add_tensor, add_tensor, h1]

lemma ι_add_eq_addQuot {n} {c : Fin n → S.C} (t1 t2 : TensorTree S c) :
    ι (t1.add t2) = addQuot (ι t1) (ι t2) := rfl

/-- The scalar multiplication of an equivalence classes of tensor trees. -/
def smulQuot {n} {c : Fin n → S.C} (r : k) :
    S.TensorTreeQuot c → S.TensorTreeQuot c := by
  refine Quot.lift (fun t => ι (smul r t)) ?_
  · intro t1 t2 h
    simp only [tensorRel] at h
    simp only
    rw [ι_apply_eq_iff_tensor_apply_eq]
    rw [smul_tensor, smul_tensor, h]

lemma ι_smul_eq_smulQuot {n} {c : Fin n → S.C} (r : k) (t : TensorTree S c) :
    ι (smul r t) = smulQuot r (ι t) := rfl

noncomputable instance commMonoid {n} (c : Fin n → S.C) : AddCommMonoid (S.TensorTreeQuot c) where
  add := addQuot
  zero := ι zeroTree
  nsmul := fun n t => smulQuot (n : k) t
  add_assoc := by
    intro a b c
    obtain ⟨a, rfl⟩ := ι_surjective a
    obtain ⟨b, rfl⟩ := ι_surjective b
    obtain ⟨c, rfl⟩ := ι_surjective c
    change addQuot (addQuot (ι a) (ι b)) (ι c) = addQuot (ι a) (addQuot (ι b) (ι c))
    rw [← ι_add_eq_addQuot, ← ι_add_eq_addQuot, ← ι_add_eq_addQuot, ← ι_add_eq_addQuot]
    rw [ι_apply_eq_iff_tensor_apply_eq]
    rw [add_assoc]
  zero_add := by
    intro a
    obtain ⟨a, rfl⟩ := ι_surjective a
    change addQuot (ι zeroTree) (ι a) = _
    rw [← ι_add_eq_addQuot, ι_apply_eq_iff_tensor_apply_eq]
    rw [TensorTree.zero_add]
  add_zero := by
    intro a
    obtain ⟨a, rfl⟩ := ι_surjective a
    change addQuot (ι a) (ι zeroTree) = _
    rw [← ι_add_eq_addQuot, ι_apply_eq_iff_tensor_apply_eq]
    rw [TensorTree.add_zero]
  add_comm := by
    intro a b
    obtain ⟨a, rfl⟩ := ι_surjective a
    obtain ⟨b, rfl⟩ := ι_surjective b
    change addQuot (ι a) (ι b) = addQuot (ι b) (ι a)
    rw [← ι_add_eq_addQuot, ← ι_add_eq_addQuot, ι_apply_eq_iff_tensor_apply_eq]
    rw [add_comm]
  nsmul_zero t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    simp only [Nat.cast_zero]
    change smulQuot ((0 : k)) (ι t) = ι zeroTree
    rw [← ι_smul_eq_smulQuot]
    rw [ι_apply_eq_iff_tensor_apply_eq]
    rw [zero_smul]
  nsmul_succ n t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    simp only [Nat.cast_add, Nat.cast_one]
    change smulQuot ((n: k) + 1) (ι t) = addQuot (smulQuot (n : k) (ι t)) (ι t)
    rw [← ι_smul_eq_smulQuot, ← ι_smul_eq_smulQuot, ← ι_add_eq_addQuot,
      ι_apply_eq_iff_tensor_apply_eq]
    simp only [smul_tensor, add_tensor]
    rw [add_smul]
    simp

noncomputable instance {n} (c : Fin n → S.C) : AddCommGroup (S.TensorTreeQuot c) :=
  {commMonoid c with
  neg t := smulQuot ((-1 : k)) t,
  zsmul n t := smulQuot n t,
  neg_add_cancel t := by
    change addQuot (smulQuot ((-1 : k)) t) t = ι zeroTree
    obtain ⟨t, rfl⟩ := ι_surjective t
    simp [← ι_smul_eq_smulQuot,  ← ι_add_eq_addQuot, ι_apply_eq_iff_tensor_apply_eq,
      smul_tensor, add_tensor]
  zsmul_zero' t := by
    simp
    change smulQuot 0 t = ι zeroTree
    obtain ⟨t, rfl⟩ := ι_surjective t
    simp [← ι_smul_eq_smulQuot, ι_apply_eq_iff_tensor_apply_eq, smul_tensor, _root_.zero_smul,
      zeroTree_tensor]
  zsmul_succ' n t := by
    simp
    change smulQuot ((n : k) + 1) t = addQuot (smulQuot (n : k) t) t
    obtain ⟨t, rfl⟩ := ι_surjective t
    simp [← ι_smul_eq_smulQuot,  ← ι_add_eq_addQuot, ι_apply_eq_iff_tensor_apply_eq,
      smul_tensor, add_tensor, add_smul]
  zsmul_neg' n t := by
    simp
    obtain ⟨t, rfl⟩ := ι_surjective t
    simp [← ι_smul_eq_smulQuot,  ← ι_add_eq_addQuot, ι_apply_eq_iff_tensor_apply_eq,
      smul_tensor, add_tensor, add_smul]
    abel
  }

instance {n} {c : Fin n → S.C} : Module k (S.TensorTreeQuot c) where
  smul r t := smulQuot r t
  one_smul t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    change smulQuot (1 : k) (ι t) = ι t
    rw [← ι_smul_eq_smulQuot]
    rw [ι_apply_eq_iff_tensor_apply_eq]
    rw [TensorTree.smul_one]
  mul_smul r s t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    change smulQuot (r * s) (ι t) = smulQuot r (smulQuot s (ι t))
    rw [← ι_smul_eq_smulQuot, ← ι_smul_eq_smulQuot,  ← ι_smul_eq_smulQuot,
      ι_apply_eq_iff_tensor_apply_eq]
    simp [smul_tensor, mul_smul]
  smul_add r t1 t2 := by
    obtain ⟨t1, rfl⟩ := ι_surjective t1
    obtain ⟨t2, rfl⟩ := ι_surjective t2
    change smulQuot r (addQuot (ι t1) (ι t2)) = addQuot (smulQuot r (ι t1)) (smulQuot r (ι t2))
    rw [← ι_smul_eq_smulQuot, ← ι_smul_eq_smulQuot,  ← ι_add_eq_addQuot, ← ι_add_eq_addQuot,
      ← ι_smul_eq_smulQuot, ι_apply_eq_iff_tensor_apply_eq]
    simp [smul_tensor, add_tensor]
  smul_zero a := by
    change smulQuot (a : k) (ι zeroTree) = ι zeroTree
    rw [← ι_smul_eq_smulQuot]
    rw [ι_apply_eq_iff_tensor_apply_eq]
    simp [smul_tensor, zero_smul]
  add_smul r s t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    change smulQuot (r + s) (ι t)  = addQuot (smulQuot r (ι t)) (smulQuot s (ι t))
    rw [← ι_smul_eq_smulQuot, ← ι_smul_eq_smulQuot,    ← ι_smul_eq_smulQuot,
      ← ι_add_eq_addQuot, ι_apply_eq_iff_tensor_apply_eq]
    simp [smul_tensor, add_tensor, add_smul]
  zero_smul t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    change smulQuot (0 : k) (ι t) = ι zeroTree
    rw [← ι_smul_eq_smulQuot]
    rw [ι_apply_eq_iff_tensor_apply_eq]
    simp [smul_tensor, zero_smul]

lemma add_eq_addQuot {n} {c : Fin n → S.C} (t1 t2 : S.TensorTreeQuot c) :
    t1 + t2 = addQuot t1 t2 := rfl

@[simp]
lemma ι_add_eq_add {n} {c : Fin n → S.C} (t1 t2 : TensorTree S c) :
    ι (t1.add t2) =  (ι t1) + (ι t2) := rfl

lemma smul_eq_smulQuot {n} {c : Fin n → S.C} (r : k) (t : S.TensorTreeQuot c) :
    r • t = smulQuot r t := rfl

@[simp]
lemma ι_smul_eq_smul {n} {c : Fin n → S.C} (r : k) (t : TensorTree S c) :
    ι (smul r t) = r • (ι t) := rfl

/-!

## Negation

-/

@[simp]
lemma ι_neg {n} {c : Fin n → S.C} (t : TensorTree S c) :
    ι (neg t) = - (ι t) := by
  change _ =  ((-1 : k)) • (ι t)
  rw [← ι_smul_eq_smul]
  rw [ι_apply_eq_iff_tensor_apply_eq]
  simp [neg_tensor, smul_tensor]

/-!

## The group action

-/

/-- The group action on an equivalence classes of tensor trees. -/
def actionQuot {n} {c : Fin n → S.C} (g : S.G) :
    S.TensorTreeQuot c → S.TensorTreeQuot c := by
  refine Quot.lift (fun t => ι (action g t)) ?_
  · intro t1 t2 h
    simp only [tensorRel] at h
    simp only
    rw [ι_apply_eq_iff_tensor_apply_eq]
    rw [action_tensor, action_tensor, h]

lemma ι_action_eq_actionQuot {n} {c : Fin n → S.C} (g : S.G) (t : TensorTree S c) :
    ι (action g t) = actionQuot g (ι t) := rfl

noncomputable instance {n} {c : Fin n → S.C} : MulAction S.G (S.TensorTreeQuot c) where
  smul := actionQuot
  one_smul t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    change actionQuot (1 : S.G) (ι t) = ι t
    rw [← ι_action_eq_actionQuot]
    rw [ι_apply_eq_iff_tensor_apply_eq]
    simp [action_tensor]
  mul_smul g h t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    change actionQuot (g * h) (ι t) = actionQuot g (actionQuot h (ι t))
    rw [← ι_action_eq_actionQuot, ← ι_action_eq_actionQuot,
      ← ι_action_eq_actionQuot, ι_apply_eq_iff_tensor_apply_eq]
    simp [action_tensor]

@[simp]
lemma ι_action_eq_mulAction {n} {c : Fin n → S.C} (g : S.G) (t : TensorTree S c) :
    ι (action g t) = g • (ι t) := rfl

/-!

## To Tensors

-/

/-- The underlying tensor for an equivalence class of tensor trees. -/
noncomputable def tensorQuot {n} {c : Fin n → S.C} :
    S.TensorTreeQuot c →ₗ[k] S.F.obj (OverColor.mk c) where
  toFun := by
    refine Quot.lift (fun t => t.tensor) ?_
    intro t1 t2 h
    simp only [tensorRel] at h
    simp only
    rw [h]
  map_add' t1 t2 := by
    obtain ⟨t1, rfl⟩ := ι_surjective t1
    obtain ⟨t2, rfl⟩ := ι_surjective t2
    rw [← ι_add_eq_add]
    change ((t1.add t2)).tensor = (t1).tensor + (t2).tensor
    simp [add_tensor]
  map_smul' r t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    rw [← ι_smul_eq_smul]
    change (smul r t).tensor = r • t.tensor
    simp [smul_tensor]

lemma tensor_eq_tensorQuot_apply {n} {c : Fin n → S.C} (t : TensorTree S c) :
    (t).tensor = tensorQuot (ι t) := rfl

lemma tensorQuot_surjective {n} {c : Fin n → S.C} : Function.Surjective (tensorQuot (c := c)) := by
  simp only [Function.Surjective]
  intro t
  use ι (tensorNode t)
  rw [← tensor_eq_tensorQuot_apply]
  simp

/-!

## Prod quotent

-/

def prodQuot {n1 n2} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C} :
    S.TensorTreeQuot c →ₗ[k] S.TensorTreeQuot c1 →ₗ[k]
      S.TensorTreeQuot (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm) := by
  refine LinearMap.mk₂ k ?_ ?_ ?_ ?_ ?_
  · refine Quot.lift₂ (fun t1 t2 => ι (prod t1 t2)) ?_ ?_
    · intro t1 t2 t3 h1
      simp only [tensorRel] at h1
      simp only
      rw [ι_apply_eq_iff_tensor_apply_eq]
      rw [prod_tensor, prod_tensor, h1]
    · intro t1 t2 t3 h1
      simp only [tensorRel] at h1
      simp only
      rw [ι_apply_eq_iff_tensor_apply_eq]
      rw [prod_tensor, prod_tensor, h1]
  · intro t1 t2 t3
    obtain ⟨t1, rfl⟩ := ι_surjective t1
    obtain ⟨t2, rfl⟩ := ι_surjective t2
    obtain ⟨t3, rfl⟩ := ι_surjective t3
    change ι (prod (add t1 t2) t3) =  ι (add (prod t1 t3) (prod t2 t3))
    rw [ι_apply_eq_iff_tensor_apply_eq]
    rw [add_prod]
  · intro n t1 t2
    obtain ⟨t1, rfl⟩ := ι_surjective t1
    obtain ⟨t2, rfl⟩ := ι_surjective t2
    change ι (prod (smul n t1) t2) =  ι (smul n (prod t1 t2))
    rw [ι_apply_eq_iff_tensor_apply_eq]
    rw [smul_prod]
  · intro t1 t2 t3
    obtain ⟨t1, rfl⟩ := ι_surjective t1
    obtain ⟨t2, rfl⟩ := ι_surjective t2
    obtain ⟨t3, rfl⟩ := ι_surjective t3
    change ι (prod t1 (add t2 t3)) =  ι (add (prod t1 t2) (prod t1 t3))
    rw [ι_apply_eq_iff_tensor_apply_eq]
    rw [prod_add]
  · intro n t1 t2
    obtain ⟨t1, rfl⟩ := ι_surjective t1
    obtain ⟨t2, rfl⟩ := ι_surjective t2
    change ι (prod t1 (smul n t2)) =  ι (smul n (prod t1 t2))
    rw [ι_apply_eq_iff_tensor_apply_eq]
    rw [prod_smul]




@[simp]
lemma ι_prod_eq_prodQuot {n n2} {c : Fin n → S.C} {c1 : Fin n2 → S.C} (t1 : TensorTree S c)
    (t2 : TensorTree S c1) :
    ι (prod t1 t2) = prodQuot (ι t1) (ι t2) := rfl

/-!

## Contr quotent

-/

TODO "Lift contrQuot to a linear  map. "

def contrQuot {n} {c : Fin (n + 1 + 1) → S.C} (i : Fin (n + 1 + 1))
    (j : Fin (n + 1))  (h : c (i.succAbove j) = S.τ (c i)) :
    S.TensorTreeQuot c →ₗ[k] S.TensorTreeQuot (c ∘ i.succAbove ∘ j.succAbove) where
  toFun := by
    refine Quot.lift (fun t => ι (contr i j h t)) ?_
    · intro t1 t2 h
      rw [ι_apply_eq_iff_tensor_apply_eq]
      simp [contr_tensor]
      simp [tensorRel] at h
      rw [h]
  map_add' t1 t2 := by
    obtain ⟨t1, rfl⟩ := ι_surjective t1
    obtain ⟨t2, rfl⟩ := ι_surjective t2
    change ι (contr i j h (t1.add t2)) = ι (add (contr i j h t1)  (contr i j h t2))
    rw [ι_apply_eq_iff_tensor_apply_eq]
    simp [contr_tensor, add_tensor]
  map_smul' r t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    change ι (contr i j h (smul r t)) = smulQuot r (ι (contr i j h t))
    rw [← ι_smul_eq_smulQuot, ι_apply_eq_iff_tensor_apply_eq]
    simp [contr_tensor, smul_tensor]

@[simp]
lemma ι_contr_eq_contrQuot {n} {c : Fin (n + 1 + 1) → S.C} (i : Fin (n + 1 + 1))
    (j : Fin (n + 1))  (h : c (i.succAbove j) = S.τ (c i)) (t : TensorTree S c) :
    ι (contr i j h t) = contrQuot i j h (ι t) := rfl


/-!

## Perm quotent

-/

TODO "Lift permQuot to a linear  map. "

def PermQuotCond {n m : ℕ} (c : Fin n → S.C) (c1 : Fin m → S.C)
      (σ : Fin n → Fin m) : Prop :=
    Function.Bijective σ ∧ ∀ i, c i = c1 (σ i)

def PermQuotCond.inv {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      {σ : Fin n → Fin m} (h : PermQuotCond c c1 σ) : Fin m → Fin n :=
  Fintype.bijInv h.1

def PermQuotCond.toEquiv {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      {σ : Fin n → Fin m} (h : PermQuotCond c c1 σ) :
      Fin n ≃ Fin m where
  toFun := σ
  invFun := PermQuotCond.inv h
  left_inv := Fintype.leftInverse_bijInv h.1
  right_inv := Fintype.rightInverse_bijInv h.1

lemma PermQuotCond.preserve_color {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      {σ : Fin n → Fin m} (h : PermQuotCond c c1 σ) :
      ∀ (x : Fin m), c1 x = (c ∘ ⇑h.toEquiv.symm) x := by
  intro x
  obtain ⟨y, rfl⟩ := h.toEquiv.surjective x
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [h.2]
  rfl

def PermQuotCond.toHom {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      {σ : Fin n → Fin m} (h : PermQuotCond c c1 σ) :
      OverColor.mk c ⟶ OverColor.mk c1 :=
    equivToHomEq (h.toEquiv) (h.preserve_color)

lemma PermQuotCond.ofHom {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      (σ  : OverColor.mk c ⟶ OverColor.mk c1) :
      PermQuotCond c c1 (Hom.toEquiv σ) := by
  apply And.intro
  · exact Equiv.bijective (Hom.toEquiv σ)
  · intro x
    simpa [OverColor.mk_hom] using Hom.toEquiv_comp_apply σ x

lemma PermQuotCond.comp {n n1 n2 : ℕ} {c : Fin n → S.C} {c1 : Fin n1 → S.C}
      {c2 : Fin n2 → S.C} {σ : Fin n → Fin n1} {σ2 : Fin n1 → Fin n2}
      (h : PermQuotCond c c1 σ) (h2 : PermQuotCond c1 c2 σ2) :
      PermQuotCond c c2 (σ2 ∘ σ) := by
  apply And.intro
  · refine Function.Bijective.comp h2.1 h.1
  · intro x
    simp only [Function.comp_apply]
    rw [h.2, h2.2]

def permQuot {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      (σ : Fin n → Fin m) (h : PermQuotCond c c1 σ) :
      S.TensorTreeQuot c →ₗ[k] S.TensorTreeQuot c1 where
  toFun := by
    refine Quot.lift (fun t => ι (perm h.toHom t)) ?_
    · intro t1 t2 h
      rw [ι_apply_eq_iff_tensor_apply_eq]
      simp [perm_tensor]
      simp [tensorRel] at h
      rw [h]
  map_add' t1 t2 := by
    obtain ⟨t1, rfl⟩ := ι_surjective t1
    obtain ⟨t2, rfl⟩ := ι_surjective t2
    change ι (perm h.toHom (t1.add t2)) = ι (add ((perm h.toHom t1))  ((perm h.toHom t2)))
    rw [ι_apply_eq_iff_tensor_apply_eq]
    simp [perm_tensor, add_tensor]
  map_smul' r t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    change ι (perm h.toHom (smul r t)) = smulQuot r (ι (perm h.toHom t))
    rw [← ι_smul_eq_smulQuot, ι_apply_eq_iff_tensor_apply_eq]
    simp [perm_tensor, smul_tensor]

@[simp]
lemma ι_perm_eq_permQuot {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) (t : TensorTree S c) :
      ι (perm σ t) = permQuot (Hom.toEquiv σ) (PermQuotCond.ofHom σ) (ι t) := by
  trans ι (perm (PermQuotCond.toHom (PermQuotCond.ofHom σ)) t)
  · congr
    exact (Hom.ext_iff σ (PermQuotCond.ofHom σ).toHom).mp (congrFun rfl)
  · rfl

lemma permQuot_ι_eq_perm {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      (σ : Fin n → Fin m) (h : PermQuotCond c c1 σ) (t : TensorTree S c) :
      permQuot σ h (ι t) = ι (perm h.toHom t) := by rfl
/-!

## Relations

-/
variable  {S : TensorSpecies k} {n n' n2 : ℕ} {c : Fin n → S.C} {c' : Fin n' → S.C}
  {c2 : Fin n2 → S.C}

def permQuotProdQuotLeft (n2 : ℕ) (σ : Fin n → Fin n') : Fin (n + n2) → Fin (n' + n2) :=
    finSumFinEquiv ∘ Sum.map σ id ∘ finSumFinEquiv.symm

lemma PermQuotCond.prod_left {σ : Fin n → Fin n'} (c2 : Fin n2 → S.C) (h : PermQuotCond c c' σ) :
    PermQuotCond (Sum.elim c c2 ∘ finSumFinEquiv.symm)
      (Sum.elim c' c2 ∘ finSumFinEquiv.symm) (permQuotProdQuotLeft n2 σ) := by
  apply And.intro
  · rw [permQuotProdQuotLeft]
    refine (Equiv.comp_bijective (Sum.map σ id ∘ ⇑finSumFinEquiv.symm) finSumFinEquiv).mpr ?_
    refine (Equiv.bijective_comp finSumFinEquiv.symm (Sum.map σ id)).mpr ?_
    refine Sum.map_bijective.mpr ?_
    apply And.intro
    · exact h.1
    · exact Function.bijective_id
  · intro i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    simp [permQuotProdQuotLeft]
    match i with
    | Sum.inl i => simp [h.2]
    | Sum.inr i => rfl

def permQuotProdQuotRight (n2 : ℕ) (σ : Fin n → Fin n') : Fin (n2 + n) → Fin (n2 + n') :=
    finSumFinEquiv ∘ Sum.map id σ ∘ finSumFinEquiv.symm

lemma PermQuotCond.prod_right {σ : Fin n → Fin n'} (c2 : Fin n2 → S.C) (h : PermQuotCond c c' σ) :
    PermQuotCond (Sum.elim c2 c ∘ finSumFinEquiv.symm)
      (Sum.elim c2 c' ∘ finSumFinEquiv.symm) (permQuotProdQuotRight n2 σ) := by
  apply And.intro
  · rw [permQuotProdQuotRight]
    refine (Equiv.comp_bijective (Sum.map id σ ∘ ⇑finSumFinEquiv.symm) finSumFinEquiv).mpr ?_
    refine (Equiv.bijective_comp finSumFinEquiv.symm (Sum.map id σ)).mpr ?_
    refine Sum.map_bijective.mpr ?_
    apply And.intro
    · exact Function.bijective_id
    · exact h.1
  · intro i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    simp [permQuotProdQuotRight]
    match i with
    | Sum.inl i => rfl
    | Sum.inr i => simp [h.2]

@[simp]
lemma prodQuot_permQuot_left {σ : Fin n → Fin n'} {h : PermQuotCond c c' σ}
    (t : S.TensorTreeQuot c) (t2 : S.TensorTreeQuot c2) :
    prodQuot (permQuot σ h t) t2 =
    permQuot (permQuotProdQuotLeft n2 σ) (h.prod_left c2) (prodQuot t t2) := by
  obtain ⟨t, rfl⟩ := ι_surjective t
  obtain ⟨t2, rfl⟩ := ι_surjective t2
  rw [permQuot_ι_eq_perm, ← ι_prod_eq_prodQuot, ← ι_prod_eq_prodQuot, permQuot_ι_eq_perm]
  rw [ι_apply_eq_iff_tensor_apply_eq]
  rw [prod_perm_left]
  rw [← ι_apply_eq_iff_tensor_apply_eq]
  simp only [Functor.id_obj, ι_perm_eq_permQuot, permProdLeft_toEquiv, ι_prod_eq_prodQuot]
  rfl

@[simp]
lemma prodQuot_permQuot_right {σ : Fin n → Fin n'} {h : PermQuotCond c c' σ}
     (t2 : S.TensorTreeQuot c2) (t : S.TensorTreeQuot c) :
    prodQuot t2 (permQuot σ h t) =
    permQuot (permQuotProdQuotRight n2 σ) (h.prod_right c2) (prodQuot t2 t) := by
  obtain ⟨t, rfl⟩ := ι_surjective t
  obtain ⟨t2, rfl⟩ := ι_surjective t2
  rw [permQuot_ι_eq_perm, ← ι_prod_eq_prodQuot, ← ι_prod_eq_prodQuot, permQuot_ι_eq_perm]
  rw [ι_apply_eq_iff_tensor_apply_eq]
  rw [prod_perm_right]
  rw [← ι_apply_eq_iff_tensor_apply_eq]
  simp only [Functor.id_obj, ι_perm_eq_permQuot, permProdRight_toEquiv, ι_prod_eq_prodQuot]
  rfl

@[simp]
lemma permQuot_permQuot {n n1 n2 : ℕ} {c : Fin n → S.C} {c1 : Fin n1 → S.C} {c2 : Fin n2 → S.C}
    {σ : Fin n → Fin n1} {σ2 : Fin n1 → Fin n2} (h : PermQuotCond c c1 σ)
    (h2 : PermQuotCond c1 c2 σ2)
    (t : S.TensorTreeQuot c) : (permQuot σ2 h2 (permQuot σ h t)) = (permQuot (σ2 ∘ σ) (h.comp h2) t) := by
  obtain ⟨t, rfl⟩ := ι_surjective t
  rw [permQuot_ι_eq_perm, permQuot_ι_eq_perm, permQuot_ι_eq_perm]
  rw [ι_apply_eq_iff_tensor_apply_eq]
  rw [perm_perm]
  congr
  exact (Hom.ext_iff (h.toHom ≫ h2.toHom) (PermQuotCond.comp h h2).toHom).mp (congrFun rfl)

lemma contrQuot_permQuot {n n' : ℕ} {c : Fin (n + 1 + 1) → S.C} {c1 : Fin (n' + 1 + 1) → S.C}
    {i : Fin (n + 1 + 1)} {j : Fin (n + 1)}
    {h : c1 (i.succAbove j) = S.τ (c1 i)} (t : S.TensorTreeQuot c)
    (σ : Fin (n + 1 + 1) → Fin (n' + 1 + 1)) (hσ : PermQuotCond c c1 σ) :
    contrQuot i j h (permQuot σ hσ t)
    = (perm (extractTwo i j σ) (contr ((Hom.toEquiv σ).symm i)
    (((Hom.toEquiv (extractOne i σ))).symm j) (S.perm_contr_cond h σ) t)).tensor := by
  rw [contr_tensor, perm_tensor, perm_tensor]
  change ((S.F.map σ) ≫ S.contrMap c1 i j h).hom t.tensor = _
  rw [S.contrMap_naturality σ]
  rfl

#lint only simpNF
end TensorTreeQuot

end TensorTree
