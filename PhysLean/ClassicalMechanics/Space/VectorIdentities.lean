/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
import PhysLean.ClassicalMechanics.Space.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!

# VectorIdentities

In this file we define common vector calculus identities based on `Space`.

-/

/-!

## General auxiliary lemmas

-/

section

variable
  {𝕜} [NontriviallyNormedField 𝕜]
  {X} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {ι : Type*} [Fintype ι] {Y' : ι → Type*} [∀ i, NormedAddCommGroup (Y' i)]
  [∀ i, NormedSpace 𝕜 (Y' i)] {Φ : X → ∀ i, Y' i} {Φ' : X →L[𝕜] ∀ i, Y' i} {x : X}

lemma ContinousLinearMap.fderiv_pi' (h : DifferentiableAt 𝕜 Φ x):
    fderiv 𝕜 Φ x = ContinuousLinearMap.pi fun i => (fderiv 𝕜 fun x => Φ x i) x:= by
  apply HasFDerivAt.fderiv
  apply hasFDerivAt_pi''
  intro i
  rw [differentiableAt_pi] at h
  exact (h i).hasFDerivAt

lemma ContDiff.differentiable_fderiv (f : X → Y) (hf : ContDiff 𝕜 2 f) :
    Differentiable 𝕜 (fun x => fderiv 𝕜 f x) := by
  have hf' : ContDiff 𝕜 (1+1) f := hf
  rw [contDiff_succ_iff_fderiv] at hf'
  apply hf'.right.right.differentiable
  decide

lemma fderiv_coord_eq_proj_comp (h : DifferentiableAt 𝕜 Φ x):
    (fderiv 𝕜 fun x => Φ x i) x = (ContinuousLinearMap.proj i).comp (fderiv 𝕜 Φ x) := by
  rw [ContinousLinearMap.fderiv_pi', ContinuousLinearMap.proj_pi]
  exact h
end

/-!

## Space.deriv lemmas

-/

namespace Space

/-- Derivatives on space distiribute over addition. -/
lemma deriv_add [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f1 f2 : Space d → M) (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    ∂[u] (f1 + f2) = ∂[u] f1 + ∂[u] f2 := by
  unfold deriv
  simp only
  ext x
  rw [fderiv_add']
  rfl
  repeat fun_prop

/-- Derivatives on space distiribute coordinate-wise over addition. -/
lemma deriv_coord_add (f1 f2 : Space d → EuclideanSpace ℝ (Fin d))
    (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    (∂[u] (fun x => f1 x i + f2 x i)) =
      (∂[u] (fun x => f1 x i)) + (∂[u] (fun x => f2 x i)) := by
  unfold deriv
  simp only
  ext x
  rw [fderiv_add]
  simp only [ContinuousLinearMap.add_apply, Pi.add_apply]
  repeat fun_prop

/-- Scalar multiplication on space derivatives. -/
lemma deriv_smul [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Space d → M) (k : ℝ) (hf : Differentiable ℝ f) :
    ∂[u] (k • f) = (k • ∂[u] f) := by
  unfold deriv
  ext x
  rw [fderiv_const_smul']
  rfl
  fun_prop

/-- Coordinate-wise scalar multiplication on space derivatives. -/
lemma deriv_coord_smul (f : Space d → EuclideanSpace ℝ (Fin d)) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∂[u] (fun x => k * f x i) x= (k • ∂[u] (fun x => f x i)) x:= by
  unfold deriv
  rw [fderiv_const_mul]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  fun_prop

/-- Derivatives on space commute with one another. -/
lemma deriv_commute [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Space d → M) (hf : ContDiff ℝ 2 f) : ∂[u] (∂[v] f) = ∂[v] (∂[u] f) := by
  unfold deriv
  ext x
  rw [fderiv_clm_apply, fderiv_clm_apply]
  simp only [fderiv_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  rw [IsSymmSndFDerivAt.eq]
  apply ContDiffAt.isSymmSndFDerivAt
  exact ContDiff.contDiffAt hf
  simp only [minSmoothness_of_isRCLikeNormedField, le_refl]
  repeat
  · apply Differentiable.differentiableAt
    apply ContDiff.differentiable_fderiv
    exact hf
  · fun_prop


/-- Coordiate functions of fderiv is differentiable. -/
lemma differentiable_fderiv_coord (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (fderiv ℝ fun x => f x i) := by
  have eq : (fderiv ℝ (fun x ↦ f x i))
      = (fun x => (ContinuousLinearMap.proj i).comp (fderiv ℝ f x)) := by
    ext x
    rw [fderiv_coord_eq_proj_comp]
    apply hf.differentiable
    decide
  rw [eq]
  apply Differentiable.clm_comp
  · fun_prop
  · apply ContDiff.differentiable_fderiv
    exact hf

/-- Second derivatives on space distiribute coordinate-wise over subtraction. -/
lemma deriv_coord_2nd_sub (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f):
    ∂[u] ((fun x => ∂[v] (fun x => f x w) x - ∂[w]  (fun x => f x v) x)) =
    (∂[u] (∂[v] (fun x => f x w))) - (∂[u] (∂[w] (fun x => f x v))) := by
  unfold deriv
  ext x
  simp only [Pi.sub_apply]
  rw [fderiv_sub]
  simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply]
  repeat
    apply Differentiable.differentiableAt
    apply Differentiable.clm_apply
    · apply differentiable_fderiv_coord
      exact hf
    · fun_prop

/-!

## Vector calculus identities

-/

lemma div_of_curl_eq_zero (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) :
    ∇⬝ (∇× f) = 0 := by
  unfold div curl Finset.sum
  simp only [Fin.isValue, Fin.univ_val_map, List.ofFn_succ, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, List.ofFn_zero, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
  ext x
  simp only [Fin.isValue, coord, basis, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
    EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Pi.zero_apply]
  rw [deriv_coord_2nd_sub, deriv_coord_2nd_sub, deriv_coord_2nd_sub]
  simp only [Fin.isValue, Pi.sub_apply]
  rw [deriv_commute fun x => f x 0, deriv_commute fun x => f x 1,
    deriv_commute fun x => f x 2]
  simp only [Fin.isValue, sub_add_sub_cancel', sub_add_sub_cancel, sub_self]
  repeat
    try apply contDiff_euclidean.mp
    exact hf

/-!

## Addition of ∇ operations

-/

lemma grad_add (f1 f2 : Space d → ℝ)
    (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2):
    ∇ (f1 + f2) = ∇ f1 + ∇ f2 := by
  unfold grad
  ext x i
  simp only [Pi.add_apply]
  rw [deriv_add]
  rfl
  exact hf1
  exact hf2

lemma div_add (f1 f2 : Space → EuclideanSpace ℝ (Fin 3))
    (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    ∇⬝ (f1 + f2) = ∇⬝ f1 + ∇⬝ f2 := by
  unfold div Finset.sum
  ext x
  simp only [coord, Pi.add_apply, basis, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
    PiLp.add_apply, EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fin.univ_val_map, List.ofFn_succ,
    Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, List.ofFn_zero, Multiset.sum_coe,
    List.sum_cons, List.sum_nil, add_zero]
  repeat rw [deriv_coord_add]
  simp only [Fin.isValue, Pi.add_apply]
  ring
  repeat assumption

lemma curl_add (f1 f2 : Space → EuclideanSpace ℝ (Fin 3))
    (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    ∇× (f1 + f2) = ∇× f1 + ∇× f2 := by
  unfold curl
  ext x i
  fin_cases i <;>
  · simp only [Fin.isValue, coord, Pi.add_apply, basis, EuclideanSpace.basisFun_apply,
    PiLp.inner_apply, PiLp.add_apply, EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fin.zero_eta]
    repeat rw [deriv_coord_add]
    simp only [Fin.isValue, Pi.add_apply]
    ring
    repeat assumption

/-!

## Scalar multiplication of ∇ operations

-/

lemma grad_smul (f : Space d → ℝ) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∇ (k • f) = k • ∇ f := by
  unfold grad
  ext x i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [deriv_smul]
  rfl
  exact hf

lemma div_smul (f : Space → EuclideanSpace ℝ (Fin 3)) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∇⬝ (k • f) = k • ∇⬝ f := by
  unfold div Finset.sum
  ext x
  simp only [coord, Pi.smul_apply, basis, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
    PiLp.smul_apply, smul_eq_mul, EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fin.univ_val_map,
    List.ofFn_succ, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, List.ofFn_zero,
    Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
  repeat rw [deriv_coord_smul]
  simp only [Fin.isValue, Pi.smul_apply, smul_eq_mul, mul_add]
  repeat fun_prop

lemma curl_smul (f : Space → EuclideanSpace ℝ (Fin 3)) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∇× (k • f) = k • ∇× f := by
  unfold curl
  ext x i
  fin_cases i <;>
  · simp only [Fin.isValue, coord, Pi.smul_apply, basis, EuclideanSpace.basisFun_apply,
    PiLp.inner_apply, PiLp.smul_apply, smul_eq_mul, EuclideanSpace.single_apply, RCLike.inner_apply,
    conj_trivial, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Fin.zero_eta]
    rw [deriv_coord_smul, deriv_coord_smul, mul_sub]
    simp only [Fin.isValue, Pi.smul_apply, smul_eq_mul]
    repeat fun_prop

/-!

## Linearity of div and curl

-/

variable {W} [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma div_linear_map (f : W → Space 3 → EuclideanSpace ℝ (Fin 3))
    (hf : ∀ w, Differentiable ℝ (f w))
    (hf' : IsLinearMap ℝ f) :
    IsLinearMap ℝ (fun w => ∇⬝ (f w)) := by
  constructor
  · intro w w'
    rw [hf'.map_add]
    rw [div_add]
    repeat fun_prop
  · intros k w
    rw [hf'.map_smul]
    rw [div_smul]
    fun_prop

lemma curl_linear_map (f : W → Space 3 → EuclideanSpace ℝ (Fin 3))
    (hf : ∀ w, Differentiable ℝ (f w))
    (hf' : IsLinearMap ℝ f) :
    IsLinearMap ℝ (fun w => ∇× (f w)) := by
  constructor
  · intro w w'
    rw [hf'.map_add]
    rw [curl_add]
    repeat fun_prop
  · intros k w
    rw [hf'.map_smul]
    rw [curl_smul]
    fun_prop
