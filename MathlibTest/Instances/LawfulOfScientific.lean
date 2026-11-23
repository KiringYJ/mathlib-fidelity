module
import Mathlib

-- Numeric tactics infer these characteristic-zero literal instances frequently.

set_option maxHeartbeats 10 in
#guard_msgs in
example : OfScientific ℚ := inferInstance

set_option maxHeartbeats 100 in
#guard_msgs in
example : OfScientific ℝ := inferInstance
