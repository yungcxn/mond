# Strings

A `string` belongs to the `compound datatypes` and are a sequence of `char`s ending with the null character `\0`.

Strings are enclosed with `"` signs.

```
string x = "test";
```

Enclosing a variable's value in strings can be done by using `{}` in a string with the variable's name in it:

```
string x = "hello";
string y = "{x} world!";
# -> "hello world!"
```

To access a char within the string, use the subscript operator `[]`:

```
string x = "hello";
char y = x[1];
# y = 'e';
```

Negative indices mean that the counting begins at the end of the string, e.g. `x[-1]` being `'o'`.

strings can contain backslashed characters for e.g. non-writable characters such as the newline `\\n`:

```
string x = "hello\nworld!";
```

strings can be concatenated via the add operator `+`:

```
string x = "hello " + "world!";
```

or multiplied (`*`) with an `int`:

```
string x = "hello" * 3;
# -> "hellohellohello"
```

or at the end subtracted with an `int` via the sub operator `-`:

```
string x = "hello" - 2;
# -> "hel"
```


## Unicode-strings

A `ustring` is technically the same as a `string`, but contains wide `uchar` characters.

Unicode-string literals must start with an `u`:

```
ustring x = u"hello";
```
