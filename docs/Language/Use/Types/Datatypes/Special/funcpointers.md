# Function pointers

Function pointers belong to the `special datatypes` as well as the pointers.

For them the `funcptr` keyword is used. Special information is needed on definition:

```
string funcptr myfptr(string, string);
```

A function pointer has a fixed return-type and set of arguments. Declaring Argument-names would be wrong.

The example function can now point to any function returning the string type whilst taking two string arguments.

Like pointers, The function can be assigned directly to other pointers, by the "points-to" operator `=>` to a value/variable or without but "ampersand'd".

dereferencing the function pointer leads to a function call:

```
myfptr => somefunc;
*myfptr("test", "abc");
```

Function pointers can also be `void` and not giving a returntype results in `void`.

```
void funcptr myptr();

# is the same as

funcptr myptr();
```
