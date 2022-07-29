# Classes

```
class name {}
```

Classes contain the following things:

  - fields
  - methods and predefined methods
  - memberclasses and membermodels

A class' predefined methods are it's constructor `$init` and it's deconstructor `$deinit`.

```
class x {
  int y;
  $init(int y) {
    $.y = y;
  }
}

x myobj = x(5);
# -> myobj.y gives 5
```

On `delete`, the class' deconstructor `$deinit` gets called.

A reference to the class itself is accessed by the predefined literal `$`.

An object (class instance) is created via:

```
class car {}

car somecar = car();  
```

Calling the constructor `car()` allocates space and returns a new object.

A class may be of a special type:

  - `con` (can't get extended)
  - `abstract`
  - `static`

```
con class x {}

class y : x {} # ILLEGAL
```

Classes can have one superclass and implement as many models as they want.


## Abstract classes / Undefined methods

Abstract classes begin with the `abstract` keyword:

```
abstract class x {}
```

All fields and methods within this type of class are of the `family` access modifier.

Abstract classes can inherit and implement other classes and models like normal.

Besides that, abstract classes are able to have `undefined method`s. Undefined methods don't have a code block and need to be overridden by it's derived class.

```
abstract class x {
  void function(int arg);
}

class y : x {
  override void function(int arg) {}
}

```

## Static classes

A static class can't be constructed, it's fields and methods behave like normal functions and variables but under the scope of a class:

```
static class x{
  void func() {}
}

x.func();
```

## Inheritance

Inheritance enables a class to get fields and methods from it's superclass.

```
class derived : base {}
```

The `:` literal indicates inheritance.
Only `public` and `family` fields and methods get inherited; Values without an access-modifier aren't accessible but theoretically existing in memory.

## Memberclasses & Membermodels

Memberclasses and membermodels are classes/models defined in the scope of other classes.

It doesn't matter if the wrapping class is `static` or not; the memberclass / -model is accessed via the wrapping class' name. Because of that, memberclasses aren't fields or methods of classes, they are just normal classes with an additional class in it's name.

```
class outer {
  class inner {}
}

outer.inner myobj = outer.inner();

```

If the wrapping class is `static` the memberclass / -model can access it's fields and methods.

Because memberclasses / -models are defined within other classes, they can have access-modifier.

```
class outer {
  model m1 {}         # only visible here
  family model m2 {}  # only visible here and for subclasses
  public model m3 {}  # visible everywhere
}
```

Memberclasses can be `static`, `abstract` and `con` aswell.

## Implementing Models

Since models enable classes to poly-implement them, a implemented field or method must be accessed via the model, the member operator `.` and the name of the field/method.

Models can be implemented via `++`:

```
model m1 {

  int somefield;

  void x();
}

model m2 {}

class y ++ m1, m2 {

  override void m1.x(){
    m1.somefield = 10;
  }

}
```


## Access-Modifier

## Override

## Operator-Support
