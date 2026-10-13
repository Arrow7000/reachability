/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/
import Lean

open Lean Elab Command

/-- `#time cmd` runs the command `cmd` and reports how long it took, in milliseconds. -/
elab "#time " cmd:command : command => do
  let start ← IO.monoMsNow
  elabCommand cmd
  logInfo m!"{(← IO.monoMsNow) - start} ms"
