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
        res + readline((str) struct {
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

typedef struct {
  int capacity;
  int len;
  int* values;
} uba;
// FIXME: use sizeof if it's added
const int UBA_SIZE = 128;
const int UBA_PREALLOC = 4096;

uba* uba_new() {
  uba* alloc = (uba*)malloc(UBA_SIZE);
  int* values = (int*)malloc(UBA_PREALLOC);

  int init_capac = UBA_PREALLOC /(int_width()/8);

  *alloc = struct {
    capacity = init_capac;
    len = 0;
    values = values;
  };

  alloc
}

void assert(bool x) {
  if (!x) {
    quit()
  }
}

void uba_free(uba* ub) {
  munmap((*ub).values, (*ub).capacity);
  munmap(ub, UBA_SIZE);
}

void uba_push() {
  
}



void repl(str inp_buf, str prompt) {
  write_all(STDOUT, prompt.dat, prompt.len);

  int read_amt = readline(inp_buf);

  write_all(STDOUT, inp_buf.dat, read_amt);

  repl(inp_buf, prompt);
}

void main() {
  char* strings = malloc(4096);

  char* prompt = strings;
  *prompt = "clac-clac>> \0";

  char* welcome = prompt + strlen(prompt) + 2;
  *welcome = "Welcome to clac.clac\n\0";

  write_all(STDOUT, welcome, strlen(welcome));

  str prompt2 = struct {
    len = strlen(prompt);
    dat = prompt;
  };

  int inplen = 0x2000;
  str inpbuf = struct {
    len = inplen;
    dat = malloc(inplen);
  };

  repl(inpbuf, prompt2);
}

main()
