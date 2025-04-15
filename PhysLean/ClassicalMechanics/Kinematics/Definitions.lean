import Mathlib.Data.Real.Basic

noncomputable section
namespace PhysLean.Kinematics

abbrev Time := ℝ
abbrev Position := ℝ
abbrev Velocity := ℝ
abbrev Acceleration := ℝ

-- Position under constant acceleration
def position (x₀ v₀ a : ℝ) (t : Time) : Position :=
  x₀ + v₀ * t + (1 / 2) * a * t^2

-- Velocity under constant acceleration
def velocity (v₀ a : ℝ) (t : Time) : Velocity :=
  v₀ + a * t

end PhysLean.Kinematics

open PhysLean.Kinematics

#check velocity      -- shows: ℝ → ℝ → ℝ → ℝ
#check velocity 2 3 4  -- confirms it

#check position      -- shows: ℝ → ℝ → ℝ → ℝ
#check position 0 5 2 3  -- confirms it
