typedef struct {
  int len;
  char* dat;
} str;

const int PROT_EXEC = 4;
const int PROT_READ = 1;
const int PROT_WRITE = 2;
const int PROT_NONE = 0;

const int MAP_PRIVATE = 2;
const int MAP_ANON = 32;

const int STDIN = 0;
const int STDOUT = 1;
const int STDERR = 2;

const int NULL = 0;

const int INT_WIDTH = 8; // native width in bytes (ASSUMED TO BE 8)

int handle_error(int res) {
  if (res == -1) {
    print(67676767);
    quit();
  }

  res
}

char *mmap(char *addr, int length, int prot, int flags, int fd, int pgoffset) {
  (char *)handle_error(syscall(0x09, (int)addr, length, prot, flags, fd, pgoffset))
}

int munmap(char* addr, int length) {
  handle_error(syscall(0x0b, (int)addr, length, 0, 0, 0, 0))
}
  
char *malloc(int size) {
  const int prot = PROT_READ + PROT_WRITE;
  const int flags = MAP_PRIVATE + MAP_ANON;

  mmap((char *)NULL, size, prot, flags, -1, 0)
}

int read(int fd, char *buf, int count) {
  syscall(0, fd, (int)buf, count, 0, 0, 0)
}

int write(int fd, char *buf, int count) {
  syscall(1, fd, (int)buf, count, 0, 0, 0)
}

int read_all(int fd, char *buf, int count) {
  int new = read(fd, buf, count);

  if (new != 0) {
    new + read_all(fd, buf + new, count - new)
  } else {
    0
  }
}

int write_all(int fd, char *buf, int count) {
  int new = write(fd, buf, count);

  if (new != 0) {
    new + write_all(fd, buf + new, count - new)
  } else {
    0
  }
}

void memcpy(char* dst, char* src, int n) {
  if (n != 0) {
    *dst = *src;
    memcpy(dst+1, src+1, n-1);
  }
}

// FIXME: add when it gets released
void int_memcpy(int* dst, int* src, int n) {
  if (n != 0) {
    *dst = *src;
    int_memcpy(dst+1, src+1, n-1);
  }
}

int strlen(char* q) {
  if ((int)(*q) == 0) {
    0
  } else {
    1 + strlen(q + 1)
  }
}

bool find_newline(char* start, int len) {
  if (len == 0) {
    false
  } else if ((int)(*start) == (int)'\n') {
    true
  } else {
    find_newline(start+1, len-1)
  }
}

int readline(str inp_buf) {
  if (inp_buf.len > 0) {
    int res = read(STDIN, inp_buf.dat, inp_buf.len);

    if (res != 0) {
      if (!find_newline(inp_buf.dat, res)) {
        res + readline(struct {
                   dat = inp_buf.dat + res;
                   len = inp_buf.len - res;
                 })
      } else {
        res
      }
    } else {
      0
    }
  } else {
    0
  }
}

void assert(bool x) {
  if (!x) {
    char* tmp = malloc(64);
    *tmp = "Assertion failure!\n\0";
    write_all(STDOUT, tmp, strlen(tmp));

    quit()
  }
}

typedef struct {
  int capacity;
  int len;
  int* values;
} uba;
// FIXME: use sizeof if it's added
const int UBA_SIZE = 128;
const int UBA_PREALLOC = 4096;

void __uba_print_helper(int* val, int len) {
  if (len != 0) {
    print(*val);
    __uba_print_helper(val + 1, len-1);
  }
}

void uba_print(uba ub) {
  __uba_print_helper(ub.values, ub.len);
}

int uba_len(uba ub) {
  ub.len
}

uba uba_new() {
  int* values = (int*)malloc(UBA_PREALLOC);
  int init_capac = UBA_PREALLOC / INT_WIDTH;

  struct {
    capacity = init_capac;
    len = 0;
    values = values;
  }
}

// FIXME -> requires mutation
// int uba_pop() {
//   int new_len = 
// }

uba uba_push(uba ub, int val) {
  // FIXME: use arrow operator when it gets released

  // FIXME: this needs to get released
  *(ub.values + ub.len) = val;
  int new_len = ub.len + 1;

  if (new_len >= ub.capacity) {
    assert(new_len == ub.capacity);

    int capacity_in_bytes = ub.capacity * INT_WIDTH;
    // realloc
    //
    int new_capacity_in_bytes = capacity_in_bytes * 2;
    int new_capacity_in_natives = new_capacity_in_bytes / INT_WIDTH;

    int* new_values = (int*)malloc(capacity_in_bytes * 2);

    int_memcpy(new_values, ub.values, ub.capacity);

    char* tmp = malloc(64);
    *tmp = "Realloc triggered!\n\0";
    write_all(STDOUT, tmp, strlen(tmp));

    print((int)new_values);
    print((int)ub.values);
    
    munmap((char*)ub.values, capacity_in_bytes);

    struct {
      capacity = new_capacity_in_natives;
      len = new_len;
      values = new_values;
    }
  } else {
    struct {
      capacity = ub.capacity;
      len = new_len;
      values = ub.values;
    }
  }
}

void uba_free(uba ub) {
  munmap((char*)ub.values, ub.capacity);
  // munmap(ub, UBA_SIZE);
}

// uba* uba_new() {
//   uba* alloc = (uba*)malloc(UBA_SIZE);
//   int* values = (int*)malloc(UBA_PREALLOC);

//   int init_capac = UBA_PREALLOC /(int_width()/8);

//   *alloc = struct {
//     capacity = init_capac;
//     len = 0;
//     values = values;
//   };

//   alloc
// }

// void uba_push(uba* ub, int val) {
//   // FIXME: use arrow operator when it gets released
//   uba der = *ub;
//   int new_len = der.len + 1;

//   if (new_len > der.capacity) {
//     // realloc
//     int* new_values = malloc(der.capacity * 2);
//   } else {
    
//   }
// }

// void uba_free(uba* ub) {
//   munmap((*ub).values, (*ub).capacity);
//   munmap(ub, UBA_SIZE);
// }


int __str_eq_helper(char* a, char* b, int len) {
  if (len == 0) {
    0
  } else if (*a == *b) {
    __str_eq_helper(a+1, b+1, len-1)
  } else {
    ((int)(*a)) - ((int)(*b))
  }
}

int strcmp(str a, str b) {
  if (a.len == b.len) {
    __str_eq_helper(a.dat, b.dat, a.len)
  } else {
    a.len - b.len
  }
}

int distance_to_space_or_newline(char* buf, int acc) {
  if (((*buf) == ' ') || ((*buf) == '\n')) {
    acc
  } else {
    distance_to_space_or_newline(buf+1, acc+1)
  }
}

typedef struct {
  str prompt;
  str quit;
  str inp_buf; 
} repl_strings;

void repl(uba ub, repl_strings strs) {
  write_all(STDOUT, strs.prompt.dat, strs.prompt.len);

  int read_amt = readline(strs.inp_buf);

  write_all(STDOUT, strs.inp_buf.dat, read_amt);

  int dtt = distance_to_space_or_newline(strs.inp_buf.dat, 0);

  print(dtt);
  if (strcmp(struct {dat = strs.inp_buf.dat; len = dtt;}, strs.quit) == 0) {
    quit();
  }

  // uba_print(ub);

  repl(uba_push(ub, 67), strs);
}

str str_from(char* cs) {
  struct {
    dat = cs;
    len = strlen(cs);
  }
}

void main() {
  char* strings = malloc(4096);

  char* prompt = strings;
  *prompt = "clac-clac>> \0";

  char* welcome = prompt + strlen(prompt) + 2;
  *welcome = "Welcome to clac.clac\n\0";
  
  char* quit = welcome + strlen(welcome) + 2;
  *quit = "quit\0";

  write_all(STDOUT, welcome, strlen(welcome));

  int inplen = 0x2000;
  str inpbuf = struct {
    len = inplen;
    dat = malloc(inplen);
  };

  repl(uba_new(), struct {
        quit = str_from(quit);
        inp_buf = inpbuf;
        prompt = str_from(prompt);
  });
}

main()
