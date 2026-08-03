# Arrays

An `array` is a fixed-size, linear list of elements of the same type.

Items of the array are accessible via the subscript operator `[]` with it's first element at index 0. If the index in the subscript is negative, counting begins at the and of the array.

Writing `[]` after a type declares the `array` type:

```
int[3] myarray;
```

Array declarations need a given length. If the array is assigned on declaration, this length isn't needed; the array-length is the same as the value being assigned to it:

```
int[] myarray = function_returning_int_array();
int[] myarray2 = [1,2,3,4];
```

An array-value begins with the start of the list `[`, its items separated by a comma and the end of the list `]`.

## Ranges

Arrays can also be created via a `range`.

Ranges are a specific notation to create an array:

```
int[] myarray = r[1..10,2];
```

The syntax `r[start..end,increment]` creates a list starting at `start` with the last value being `end` while incrementing `start` always by the `increment` number.

A Range can also be `r[..10]` if no increment or startvalue is chosen. Then, the start value is `0` and the increment `1` by default.
