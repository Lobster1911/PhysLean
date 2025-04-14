/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.FieldSpecification.Basic
/-!

# Yukawa Theory

The Yukawa thoery (named after Hideki Yukawa) is a quantum field theory
consisting of a real scalar field and a Dirac fermion.

The main interaction term in the Yukawa theory is the Yukawa interaction,
which in the Standard model appears as a coupling between the Higgs field and the fermion fields.

-/

namespace YukawaTheory

inductive Fields
  | scalar : Fields
  | fermion : Fields
deriving Inhabited, BEq, DecidableEq

def fieldSpecification : FieldSpecification where
  Field := Fields
  statistic f :=
    match f with
    | Fields.scalar => FieldStatistic.bosonic
    | Fields.fermion => FieldStatistic.fermionic
  PositionLabel f :=
    match f with
    | Fields.scalar => Unit
    | Fields.fermion => Fin 4 × Fin 2
  AsymptoticLabel f :=
    match f with
    | Fields.scalar => Unit
    | Fields.fermion => Fin 2 × Fin 2

end YukawaTheory
