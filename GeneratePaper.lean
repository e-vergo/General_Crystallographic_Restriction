/-
Generate HTML output from the Crystallographic Paper document.
This executable produces `.lake/build/verso/paper_verso.html`.
-/
import SBSBlueprint
import Crystallographic.Paper

open Verso.Genre.SBSBlueprint.Main

def main : IO UInt32 :=
  sbsBlueprintMain (%doc Crystallographic.Paper) (config := {
    outputDir := ".lake/build/verso",
    buildDir := ".lake/build",
    title := "The Crystallographic Restriction Theorem",
    outputFileName := "paper_verso",
    verbose := true,
  })
