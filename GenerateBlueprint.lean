/-
Generate HTML output from the Crystallographic Blueprint document.
This executable produces `.lake/build/verso/blueprint_verso.html`.
-/
import SBSBlueprint
import Crystallographic.Blueprint

open Verso.Genre.SBSBlueprint.Main

def main : IO UInt32 :=
  sbsBlueprintMain (%doc Crystallographic.Blueprint) (config := {
    outputDir := ".lake/build/verso",
    buildDir := ".lake/build",
    title := "The Crystallographic Restriction Theorem",
    outputFileName := "blueprint_verso",
    verbose := true,
  })
