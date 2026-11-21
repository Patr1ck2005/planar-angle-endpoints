import FiveCanonicalWords
import OrderOrbitCore
namespace R67.Five
theorem representative_mem : ∀ r : Fin 20,
    (List.ofFn (fun s : Fin 10=>(R67.OrderOrbit.representative r s).val))∈canonical := by decide +kernel
end R67.Five
#print axioms R67.Five.representative_mem
