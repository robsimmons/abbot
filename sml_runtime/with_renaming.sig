signature WITH_RENAMING = sig
    type 'oper t = Renaming.t * 'oper

    val apply_renaming : Renaming.t -> 'oper t -> 'oper t
end
