# Global variables

Variables outside of any function, class or other scopes are considered to be global. They begin with the `glob` keyword:

```
glob int variable;
glob char somechar = '\n';
```

Global variables behave like normal variables; they can be assigned to anything or declared on definition.

reassignment outside of functions is not possible.

Global variables can be constant by using `con`.

```
glob con int CONSTANT_X = 10;
```
