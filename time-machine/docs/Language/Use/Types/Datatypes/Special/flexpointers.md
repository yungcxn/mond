# Flex(-ible) pointers

The `flexptr` belongs to the `special datatypes`.

It behaves the same way a normal `ptr` does, but without a declared type being pointed to. This allows the pointer C-like "void pointer" behaviour.

```
flexptr variable = &someint;
variable = &somechar;
```

before dereferencing, the pointer needs to be casted to a type:

```
flexptr variable = &somechar;
char somechar = *((char) variable);
```

typecasting a flexptr doesn't change the type of the variable from `flexptr` to the given type; it only changes the type being pointed to.
