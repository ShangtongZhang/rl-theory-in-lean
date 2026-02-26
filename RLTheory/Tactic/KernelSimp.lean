import Mathlib

open Lean Elab Tactic in
syntax (name := kernelSimp) "kernel_simp" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| kernel_simp) =>
    `(tactic| simp only [
        ProbabilityTheory.Kernel.map_comp,
        ProbabilityTheory.Kernel.map_comp_right,
        ProbabilityTheory.Kernel.id_comp,
        ProbabilityTheory.Kernel.comp_id,
        ProbabilityTheory.Kernel.map_id,
        ProbabilityTheory.Kernel.id_map,
        ProbabilityTheory.Kernel.fst_map_prod,
        ProbabilityTheory.Kernel.snd_map_prod,
        Function.comp_id, Function.id_comp, Function.comp_assoc])
  | `(tactic| kernel_simp [$lemmas,*]) =>
    `(tactic| simp only [
        ProbabilityTheory.Kernel.map_comp,
        ProbabilityTheory.Kernel.map_comp_right,
        ProbabilityTheory.Kernel.id_comp,
        ProbabilityTheory.Kernel.comp_id,
        ProbabilityTheory.Kernel.map_id,
        ProbabilityTheory.Kernel.id_map,
        ProbabilityTheory.Kernel.fst_map_prod,
        ProbabilityTheory.Kernel.snd_map_prod,
        Function.comp_id, Function.id_comp, Function.comp_assoc,
        $lemmas,*])
