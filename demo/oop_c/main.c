#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// ==== 宏定义 ====
// 用于拼接字符串，例如 concat(Base, _init) 会被替换为 Base_init。## 表示连接两个 token
#define concat(a, b) a##b
// 首先分配内存，然后调用构造函数TYPE_init。最后返回指向新对象的指针。这使用了“块表达式”，它会在一个代码块中执行多个语句，并返回最后一个语句的值（这里的TMP）。
#define NEW(TYPE, ...)                                                         \
  ({                                                                           \
    TYPE *TMP = (TYPE *)malloc(sizeof(TYPE));                                  \
    concat(TYPE, _init)(TMP, ##__VA_ARGS__);                                   \
    TMP;                                                                       \
  })
// 调用虚函数表中的函数。
#define VCALL(obj, func, ...) (((obj).vTable)->func(&(obj), ##__VA_ARGS__))
// 调用析构函数。
#define DELETE(obj_ptr)                                                        \
  do {                                                                         \
    VCALL(*obj_ptr, teardown);                                                 \
    free(obj_ptr);                                                             \
  } while (0)

// ==== 基类定义与实现 ====
typedef struct Base Base;
typedef struct BaseVTable BaseVTable;

struct Base {
  BaseVTable *vTable;
  char *name;
};

struct BaseVTable {
  void (*teardown)(void *self);
  void (*print)(void *self);
};


void Base_teardown(void *self) {
  Base *obj = (Base *)self;
  free(obj->name);
}

void Base_print(void *self) {
  Base *obj = (Base *)self;
  printf("Base: %s\n", obj->name);
}
void Base_init(Base *self, const char *name) {
  static BaseVTable vTable = {.teardown = NULL, .print = NULL};
  self->vTable = &vTable;
  self->name = strdup(name);
  if (!vTable.teardown)
    vTable.teardown = Base_teardown;
  if (!vTable.print)
    vTable.print = Base_print;
}

// ==== 派生类定义与实现 ====
typedef struct Derived Derived;

struct Derived {
  Base base;
  int value;
};


void Derived_teardown(void *self) {
  Derived *obj = (Derived *)self;
  printf("Derived destructor called for: %s\n", obj->base.name);
  Base_teardown(self);
}

void Derived_print(void *self) {
  Derived *obj = (Derived *)self;
  printf("Derived: %s, value: %d\n", obj->base.name, obj->value);
}
void Derived_init(Derived *self, const char *name, int value) {
  Base_init((Base *)self, name);
  self->value = value;

  static BaseVTable vTable = {.teardown = NULL, .print = NULL};
  self->base.vTable = &vTable;
  if (!vTable.teardown)
    vTable.teardown = Derived_teardown;
  if (!vTable.print)
    vTable.print = Derived_print;
}

// ==== 主程序 ====
int main() {
  // 创建 Base 对象
  Base *base = NEW(Base, "Base Object");
  VCALL(*base, print); // 调用 Base 的虚函数
  DELETE(base);        // 销毁 Base 对象

  // 创建 Derived 对象
  Derived *derived = NEW(Derived, "Derived Object", 42);
  VCALL(derived->base, print); // 调用 Derived 的虚函数
//   DELETE(derived);             // 销毁 Derived 对象

  return 0;
}
