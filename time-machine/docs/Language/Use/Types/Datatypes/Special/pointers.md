# Pointers

The pointer type belongs to the `special datatypes`,
having extra operators and syntax.

A normal pointer's size is 8 bytes and only points to a memory location where a single value is stored. Objects and variables of datatypes but not functions.

They can point to other function pointers.

The `ptr` keyword defines pointers:

```
string ptr ptrvar;
```

A pointer needs to have it's type named before. Leaving the type blank doesn't initiate a C-like "void" pointer.

Pointers can be assigned to other pointers, meaning they point to the same location.

```
ptrvar = otherstringptr;
```

Besides that, they are assigned to memory locations of other variables / values via the ampersand operator `&`.

```
ptrvar = &somestring;
```

If there is no personal favour in getting the memory location at first, the "pointing-to" operator `=>` can be used:

```
ptrvar => somestring;
```

The dereference operator `*` allows to get the value of the memory location it's being pointed on.

C-like dereferencing on assignment is not possible, but this is:

```
ptrvar = otherstringptr;
# is the same as
ptrvar => *otherstringptr;
```
