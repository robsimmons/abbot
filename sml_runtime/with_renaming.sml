structure With_renaming :> WITH_RENAMING = struct
type 'oper t = Renaming.t * 'oper

fun apply_renaming renaming (renaming', oper) = (Renaming.compose renaming renaming', oper)
end
