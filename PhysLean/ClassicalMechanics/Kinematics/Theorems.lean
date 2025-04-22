import ClassicalMechanics.Kinematics.Equations
import Mathlib
import PhysLean.Kinematics.Definitions

open PhysLean.Kinematics

namespace PhysLean.Kinematics

theorem position_at_zero (x₀ v₀ a : ℝ) :
  position x₀ v₀ a 0 = x₀ := by
  simp [position]

theorem velocity_at_zero (v₀ a : ℝ) :
  velocity v₀ a 0 = v₀ := by
  simp [velocity]

end PhysLean.Kinematics

#check position_at_zero
