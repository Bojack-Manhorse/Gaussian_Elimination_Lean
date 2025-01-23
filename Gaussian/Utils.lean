import Mathlib.Algebra.Module.Defs
import ZKLib.Data.UniPoly

namespace Utils

structure vector_one (β : Type) [Field β] (m : {x : ℕ // x > 1}) where
  vector : Vector β m
  last_entry_is_one : vector[m.1 - 1]'(by omega) = 1



end Utils
