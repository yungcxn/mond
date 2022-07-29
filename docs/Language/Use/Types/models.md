# Models

```
model m {}
```

Models can be compared to "interfaces" in Java.

They contain fields and undefined Methods, which are functions without code-blocks, that need to be overridden by the class implementing those.

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
