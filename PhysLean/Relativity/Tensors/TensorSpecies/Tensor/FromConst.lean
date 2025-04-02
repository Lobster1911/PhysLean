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

/-- A general constant node. -/
def fromConst {n : ℕ} {c : Fin n → S.C} (T : 𝟙_ (Rep k S.G) ⟶ S.F.obj (OverColor.mk c)) :
    Tensor S c :=  (T.hom (1 : k))

/-- A constant two tensor (e.g. metric and unit). -/
noncomputable def fromConstPair {c1 c2 : S.C}
      (v : 𝟙_ (Rep k S.G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2)) :
      S.Tensor ![c1, c2] := (OverColor.Discrete.pairIsoSep S.FD).hom.hom (v.hom (1 : k))

/-- Tensors formed by `fromConstPair` are invariant under the group action. -/
@[simp]
lemma actionT_fromConstPair {c1 c2 : S.C}
    (v : 𝟙_ (Rep k S.G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2))
    (g : S.G) : (g • (fromConstPair v)) = (fromConstPair v) := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, actionT_eq,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    fromConstPair]
  change ((Discrete.pairIsoSep S.FD).hom.hom ≫
    ModuleCat.ofHom ((S.F.obj (OverColor.mk ![c1, c2])).ρ g)) (v.hom _) = _
  erw [← (Discrete.pairIsoSep S.FD).hom.comm g]
  change ((v.hom ≫ ModuleCat.ofHom ((S.FD.obj { as := c1 } ⊗ S.FD.obj { as := c2 }).ρ g)) ≫
    (Discrete.pairIsoSep S.FD).hom.hom) _ = _
  erw [← v.comm g]
  simp

end Tensor

end TensorSpecies
