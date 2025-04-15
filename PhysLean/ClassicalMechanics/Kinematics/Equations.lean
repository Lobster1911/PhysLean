import PhysLean.Kinematics.Definitions
import Mathlib.Tactic

namespace PhysLean.Kinematics

-- The velocity is the derivative of position
theorem velocity_is_derivative (x₀ v₀ a : ℝ) :
    ∀ t, deriv (position x₀ v₀ a) t = velocity v₀ a t := by
  intro t
  simp [position, velocity]
  norm_num
  ring


end PhysLean.Kinematics
