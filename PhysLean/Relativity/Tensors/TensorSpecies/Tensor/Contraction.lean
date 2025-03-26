/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.TensorSpecies.Tensor.Basic
/-!

# Contractions of tensors

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {S : TensorSpecies k}

namespace Tensor

noncomputable def Pure.contrPCoeff {n : ℕ} {c : Fin (n + 1 + 1) → S.C} (i : Fin (n + 1 + 1))
    (j : Fin (n + 1)) (hij : c (i.succAbove j) = S.τ (c i)) (p : Pure S c) : k :=
    (S.contr.app (Discrete.mk (c i)))
      (p i ⊗ₜ ((S.FD.map (eqToHom (by simp [hij]))) (p (i.succAbove j))))

lemma Pure.contrPCoeff_update_of_neq {n : ℕ} {c : Fin (n + 1 + 1) → S.C} {i : Fin (n + 1 + 1)}
    {j : Fin (n + 1)} {hij : c (i.succAbove j) = S.τ (c i)} {p : Pure S c}
    {k : Fin (n + 1 + 1)} {x :  S.FD.obj (Discrete.mk (c k))} (hk : k ≠ i ∧ k ≠ i.succAbove j) :
    (p.update k x).contrPCoeff i j hij = p.contrPCoeff i j hij := by
  rw [contrPCoeff]
  congr
  · rw [update, Function.update_of_ne]
    exact Ne.symm hk.1
  · rw [update, Function.update_of_ne]
    exact Ne.symm hk.2

@[simp]
lemma Pure.contrPCoeff_update_fst_add {n : ℕ} {c : Fin (n + 1 + 1) → S.C} {i : Fin (n + 1 + 1)}
    {j : Fin (n + 1)} {hij : c (i.succAbove j) = S.τ (c i)}
    {x y :  S.FD.obj (Discrete.mk (c i))} {p : Pure S c} :
    (p.update i (x + y)).contrPCoeff i j hij  =
    (p.update i x).contrPCoeff i j hij + (p.update i y).contrPCoeff i j hij := by
  simp [contrPCoeff, update, TensorProduct.add_tmul, map_add]
  change ((S.contr.app { as := c i })).hom.hom' _ = ((S.contr.app { as := c i })).hom.hom' _
    + ((S.contr.app { as := c i })).hom.hom' _
  simp
  congr 4
  · rw [Function.update_of_ne, Function.update_of_ne]
    · exact Fin.succAbove_ne i j
    · exact Fin.succAbove_ne i j
  · rw [Function.update_of_ne, Function.update_of_ne]
    · exact Fin.succAbove_ne i j
    · exact Fin.succAbove_ne i j

@[simp]
lemma Pure.contrPCoeff_update_snd_add {n : ℕ} {c : Fin (n + 1 + 1) → S.C} {i : Fin (n + 1 + 1)}
    {j : Fin (n + 1)} {hij : c (i.succAbove j) = S.τ (c i)}
    {x y :  S.FD.obj (Discrete.mk (c (i.succAbove j)))} {p : Pure S c} :
    (p.update (i.succAbove j) (x + y)).contrPCoeff i j hij  =
    (p.update (i.succAbove j) x).contrPCoeff i j hij +
      (p.update (i.succAbove j) y).contrPCoeff i j hij := by
  simp [contrPCoeff, update, TensorProduct.add_tmul, map_add]
  change ((S.contr.app { as := c i })).hom.hom' _ = ((S.contr.app { as := c i })).hom.hom' _
    + ((S.contr.app { as := c i })).hom.hom' _
  rw [Function.update_of_ne (Fin.ne_succAbove i j), Function.update_of_ne (Fin.ne_succAbove i j),
    Function.update_of_ne (Fin.ne_succAbove i j)]
  conv_lhs =>
    enter [2, 3]
    change ((S.FD.map (eqToHom _))).hom.hom' (x + y)
  simp [contrPCoeff, update, TensorProduct.tmul_add, map_add]
  rfl

/-- The contraction of indices of a pure tensor. This is a map into
  `Tensor c` as when `n = 0` it does not give back a pure tensor. -/
noncomputable def Pure.contrP {n : ℕ} {c : Fin (n + 1 + 1) → S.C} (i : Fin (n + 1 + 1))
    (j : Fin (n + 1)) (hij : c (i.succAbove j) = S.τ (c i)) (p : Pure S c) :
    S.Tensor (c ∘ i.succAbove ∘ j.succAbove) :=
    (p.contrPCoeff i j hij) • ((p.drop i).drop j).toTensor

@[simp]
lemma Pure.contrP_update_add {n : ℕ} {c : Fin (n + 1 + 1) → S.C} (i : Fin (n + 1 + 1))
    (j : Fin (n + 1)) (hij : c (i.succAbove j) = S.τ (c i)) (p : Pure S c)
    (k : Fin (n + 1 + 1)) (x y :  S.FD.obj (Discrete.mk (c k))) :
    (update p k (x + y)).contrP i j hij =
    (update p k x).contrP i j hij + (update p k y).contrP i j hij := by
  rw [contrP, contrP, contrP]
  by_cases hk : k ≠ i ∧ k ≠ i.succAbove j
  · rw [Pure.contrPCoeff_update_of_neq hk, Pure.contrPCoeff_update_of_neq hk,
        Pure.contrPCoeff_update_of_neq hk]
    rw [← smul_add]
    congr
    have hk' := Fin.eq_self_or_eq_succAbove i k
    simp_all
    obtain ⟨k, rfl⟩ := hk'
    simp
    rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hk
    have hk' := Fin.eq_self_or_eq_succAbove j k
    simp_all
    obtain ⟨k, rfl⟩ := hk'
    simp
  · rw [Mathlib.Tactic.PushNeg.not_and_or_eq] at hk
    simp at hk
    rcases hk with rfl | rfl
    · simp [add_smul]
    · simp [add_smul]


lemma Pure.contrP_update_smul {n : ℕ} {c : Fin (n + 1 + 1) → S.C} (i : Fin (n + 1 + 1))
    (j : Fin (n + 1)) (hij : c (i.succAbove j) = S.τ (c i)) (p : Pure S c)
    (m : Fin (n + 1 + 1)) (r : k) (x :  S.FD.obj (Discrete.mk (c m))) :
    (update p m (r • x)).contrP i j hij =
    r • (update p m x).contrP i j hij := by
  sorry

noncomputable def contrT {n : ℕ} {c : Fin (n + 1 + 1) → S.C} (i : Fin (n + 1 + 1))
    (j : Fin (n + 1)) (hij : c (i.succAbove j) = S.τ (c i)) :
    Tensor S c →ₗ[k] Tensor S (c ∘ i.succAbove ∘ j.succAbove) :=
    Basis.constr (basis c) k fun b => ((Pure.basisVector c b).contrP i j hij).toTensor

lemma contrT_pure {n : ℕ} {c : Fin (n + 1 + 1) → S.C} (i : Fin (n + 1 + 1))
    (j : Fin (n + 1)) (hij : c (i.succAbove j) = S.τ (c i)) (p : Pure S c) :
    contrT i j hij p.toTensor = (p.contrP i j hij).toTensor := by
  sorry

end Tensor

end TensorSpecies
