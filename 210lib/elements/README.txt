This file contains a bunch of structures/functors that ascribe to the
ELEMENT signature. The basic types such as ints, bools, and strings are
in structures. The polymorphic types are inside of functors which use
a sub element as the alpha. structures ascribing to the element signature
are expected to implement the following things:

    type t (the type of the element)

    toString : t -> string (converts the element to a string representation)

    equals : t * t -> bool (compares to elements and determines if they are
    	       	      	    equal)


