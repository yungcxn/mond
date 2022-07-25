# Macros

mondpre (first compiler part) preprocesses macros.
They aren't recognized by any language specifications.

The macro operator is `%`.

How to call a macro:

```
%incl file.mon;
%getter char, somechar;
```

## Macro-Usage

The macroname `incl` or `getter` need to be directly after the `%`.
The arguments are separated by a comma and parsed without space-characters into a wordlist.

For arguments containing spaces string, semicolons or the macro operator, literals are introduced:

```
%incl "folder with space/file.mon";
%incl "folder;with%special signs/file.mon";
```

NOTE: Using backslashes to write characters is not possible! backslashes are still parsed as the c-like syntax '\\'.


## 1. Include (`%incl`)

includes given directory into the .mon file.

takes 1 argument to determine relative file path

```
%incl file/path.mon;
```


## 2. Flag (`%flag`)

sets a preprocessor flag; saves given string for later preprocessing (e.g. flag-request).

takes 1 argument, the flag string:

```
%incl _CUSTOM_FLAG;
```

flag names are _UPPER_SNAKE_CASE by convention, but they can be any string.

## 3. Flag-Request (`%isset`)

produces a boolean value (`true`, `false`) whether a flag is currently defined or not.

takes 1 argument, the flag string:

```
%isset _CUSTOM_FLAG;
```

## 4. Getter (`%getter`)

produces a getter function `get_name()`, while name being the given argument;

can take up to 3 arguments, the first being a access-modifier, the second one the type of the field given as the third argument. If argument 1 isn't given, then argument 1 is the type.
if only one argument is used, it's the variable.

```
%getter public, int, someint;
%getter int, someint;
%getter someint;

# everything produces:

public int get_someint() {
  return $.someint;
}

int get_someint() {
  return $.someint;
}

(typeof someint) get_someint() {
  return $.someint;
}
```

## 4. Setter (`%setter`)

works the same as `%getter`, produces setter function `set_name()`

```
%setter public, int, someint;
%setter int, someint;
%setter someint;

# everything produces:

public void set_someint(int x) {
  $someint = x;
}

void set_someint(int x) {
  $someint = x;
}

void set_someint((typeof someint) x) {
  $someint = x;
}
```

## 4. Xetter (`%xetter`)

works the same as `%getter` and `%setter`, produces both getter function `get_name()` and setter function `set_name()`.

```
%xetter public, int, someint;
%xetter int, someint;
%xetter someint;
```
