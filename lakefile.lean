import Lake
open Lake DSL

package GreedyUniformity where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "c55e6e786f49471c72fbddbec5415808896aec1e"

@[default_target]
lean_lib GreedyUniformity

lean_lib Challenge

lean_lib Solution
