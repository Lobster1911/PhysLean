/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Informal.Post
import Mathlib.Lean.CoreM
import PhysLean.Meta.AllFilePaths
/-!

# Local stats within PhysLean

Given a directory this script returns the statistics of
the lean files contained within.

It currently returns the number of files, the number of definitions and the number
of lemmas.

-/

open Lean System Meta PhysLean


def numDefs (dir : String) : CoreM Nat := do
  let imports ← PhysLean.allImports
  let x ← imports.mapM PhysLean.Imports.getUserConsts
  let dirName := dir.replace "./" ""
  let dirName := dirName.replace ".lean" ""
  let dirName := dirName.replace "/" "."
  x.flatFilterSizeM fun c => return c.isDef && (← c.name.hasPos)
   && (← Lean.Name.fileName c.name).toString.startsWith dirName

def numLemmas (dir : String) : CoreM Nat := do
  let imports ← PhysLean.allImports
  let x ← imports.mapM PhysLean.Imports.getUserConsts
  let dirName := dir.replace "./" ""
  let dirName := dirName.replace ".lean" ""
  let dirName := dirName.replace "/" "."
  x.flatFilterSizeM fun c => return !c.isDef && (← c.name.hasPos)
   && (← Lean.Name.fileName c.name).toString.startsWith dirName

def getStats (dir : String ) : MetaM String := do
  let noDefsVal ← numDefs dir
  let noLemmasVal ← numLemmas dir
  let s := s!"
    Number of Definitions (incl. instances): {noDefsVal}
    Number of Lemmas: {noLemmasVal}"
  pure s

unsafe def main (args  : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | [dir] => do
  let files ← allFilePaths.go (#[] : Array FilePath) dir (dir : FilePath)
  let noFiles := files.size
  let statString ← CoreM.withImportModules #[`PhysLean] (getStats dir).run'
  println! statString

  println! s!"Number of files: {noFiles}"
  pure 0
  | _ => do
    IO.println s!"This script requires a directory."
    pure 1
