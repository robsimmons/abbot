functor MkTreapTable(structure HashKey : HASHKEY) : TABLE =
  MkBSTTable(structure Tree = MkTreap(structure HashKey = HashKey)
             structure Seq = ArraySequence)
