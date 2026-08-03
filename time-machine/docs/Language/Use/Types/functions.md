# Functions

Functions may take arguments, may compute by using control structurs, may do other operations and may return a value.

Functions need to have a return type. Giving no return type results in `void`:

```
void somefunction() {}

# is the same as

somefunction() {}
```

Arguments are listed in the function-call operator `()`, separated by a comma:

```
int somefunction(int arg1, string arg2) { return 0; }
```

a function is identical if all three conditions are given:

1. Same name
2. Same return type
3. Same argument types in the same order

Functions can't be reassigned, they can only be assigned to pointers without the function-call operator `()`.

## Return values

Functions can return any of the following types:

- any datatype (`basic` & `compounds`)
- `flexptr`
- `ptr`
- `funcptr`
- `void`
- any `object`s of a defined `class`

the syntax for the special datatypes is always the same; imagine declaring a variable and appending the function-call operator `()` and a code block via `{}`:

```
flexptr myfunc1() {...}

string ptr myfunc2() {...}

int funcptr myfunc3(string, string)(int arg2, int arg3) {...}

void funcptr myfunc4()() {...}

int[] myfunc5() {...}
```

`myfunc2` returns a pointer to the `string` type.
`myfunc3` returns a functionpointer which returns an `int` and takes two `string`s. `myfunc3` itself takes two `int`s as argument.
`myfunc4` returns a functionpointer to a void-function both returning and taking nothing.
`myfunc1` and `myfunc5` are self-explanatory.

If the function being pointed by the function pointer returned by `myfunc3` wants to be called, use this:

```
*(myfunc3(1,2))("string1", "string2");
```

here `myfunc3(1,2)` returns the function pointer, which needs to be dereferenced before using the function-call operator `()` with the arguments of two strings.

## Arguments

Function-arguments behave the same way like declaring a variable. Function pointers for example can be arguments like this:

```
void myfunc(void funcptr arg1(int, int)) {}
```

`arg1` is a function pointer to a void-function taking two integers as arguments.

To separate call-by-value and call-by-reference, `con` is used to determine that a value passed as an argument is copied and wouldn't change the passed argument itself.

```
void myfunc(con int arg1, int arg2) {}
```

here `arg1` can be changed, but the passed variable isn't changed, only it's value copied into `arg1`.

## Inline functions

Functions can be defined in functions, meaning these inline functions can only be called inside it's defined scope.

```
void outerfunction() {
  void innerfunc() {}

  innerfunc();
}
```

inline functions can also be returned as `funcptr`s pointed to them.

## Lambda-Syntax

The classic syntax of `int myfunc(int i) {return i + 2;}` can be transformed into `int myfunc(int i) -> (i+2);`.

This is for functions only having a return statement, not computing other things such as bare, void function calls or control structures. The syntax can be seen as the following pseudocode:

```
type name(type1 arg1, type2 arg) -> (returnstatement);
```

## Undefined-(Method)-Syntax

Methods in Models or sometimes in abstract classes need to be undefined, which means that no code-block is defined:

```
abstract class x{
  void y();
}

class z : x{
  override void y() {}
}
```

Note: This only occurs in classes
