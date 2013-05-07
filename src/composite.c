/*  Composite SMT Solver
 *  Will Blair and Nikka Ghalili
 *  CS512 Final Project
 */
#include <zmq.h>
#include <pthread.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <stdint.h>
#include <string.h>
#include <sched.h>

//ZMQ Context is Shared
static void* context;

static pid_t procs[2];

#define LOG 1

typedef enum {
  UNSAT,
  UNKNOWN,
  SAT,
  FINISHED
} answer;

typedef enum {
  YICES,
  Z3
} solver;

typedef struct {
  void *socket;
  int read;
  uint32_t solver;
} worker_args;

void * control_worker(void *socket) {
  int checked = 0;
  //{Status, Solver, Message ID}
  uint32_t buf[3];

  while(1) {
    int read = zmq_recv(socket, buf, sizeof(buf), 0);

    assert(read != -1);

    //Don't display something we've already checked
    if(buf[2] < checked && buf[0] != FINISHED) {
#if LOG
      if(buf[1] == Z3) {
        printf("Z3");
      } else {
        printf("Yices");
      }
      printf(" lost check-sat #%d\n", buf[2]);
#endif
      continue;
    }
    
    switch(buf[0]) {
    case UNSAT: 
      printf("unsat\n");
      break;
    case SAT:
      printf("sat\n");
      break;
    case UNKNOWN:
      printf("unknown");
      break;
    case FINISHED:
#if LOG
      if(buf[1] == Z3) {
        printf("Z3");
      } else {
        printf("Yices");
      }
      printf(" wins!\n");
#endif
      fflush(stdout);
      exit(0);
    }
    checked++;
  }
  return NULL;
}

void * solver_worker(void *args) {
  worker_args *params = args;
  FILE *solver = fdopen(params->read, "r");
  
  assert(solver != NULL);
  
  char buf[128];
  uint32_t msg[3];
  int checked = 0;

  while(fgets(buf, 128, solver) != NULL) {
    if(strcmp(buf, "unsat\n") == 0) {
      msg[0] = UNSAT;
      msg[1] = params->solver;
      msg[2] = checked++;
      zmq_send (params->socket, msg, sizeof(msg), 0);
    } else if (strcmp(buf, "sat\n") == 0) {
      msg[0] = SAT;
      msg[1] = params->solver;
      msg[2] = checked++;
      zmq_send (params->socket, msg, sizeof(msg), 0);
    } else if (strcmp(buf, "unknown\n") == 0) {
      msg[0] = UNKNOWN;
      msg[1] = params->solver;
      msg[2] = checked++;
      zmq_send (params->socket, msg, sizeof(msg), 0);
    }
  }

  msg[0] = FINISHED;
  msg[1] = params->solver;
  msg[2] = checked;
  zmq_send (params->socket, msg, sizeof(msg), 0);
  
  while(1);
  return NULL;
}

void start_worker(solver s, void *sock, int read) {
  pthread_t t; 
  worker_args *args = malloc(sizeof(worker_args));
  args->solver = s;
  args->socket = sock;
  args->read = read;
  pthread_create(&t, NULL, solver_worker, (void*)args);
}

void start_solver(solver s, int read, int write) {
  pid_t running;
  int status;
  
  if((running = fork()) < 0) {
    fprintf(stderr, "Couldn't fork");
    exit(1);
  } else if (running > 0) {
    procs[s] = running;
    close(write);
    return ;
  }
  
  status = dup2(read, STDIN_FILENO);
  assert(status >= 0);
  
  status = dup2(write, STDOUT_FILENO);
  assert(status >= 0);
  
  char *  const yices_buf[2] = {"yices2", NULL};
  char * const z3_buf[4] = {"z3", "-smt2", "-in", NULL};

  switch(s) {
  case YICES:
    execvp("./yices2", yices_buf);
    break;
  case Z3:
    execvp("z3", z3_buf);
    break;
  }
  fprintf(stderr, "Couldn't start a solver\n");
  exit(1);
}
    
int main (int argc, char *argv[]) {
  int from_z3[2];
  int from_yices[2];

  int status;
  
  if (argc < 2) {
    fprintf(stderr, "usage: %s file\n", argv[0]);
    exit(1);
  }
  
  FILE *z3file = fopen(argv[1], "r");
  FILE *yicesfile = fopen(argv[1], "r");
  
  assert(z3file != NULL);
  assert(yicesfile != NULL);

  //Set up the pipes to talk to the solvers
  
  status = pipe(from_z3);
  assert(status == 0);
  
  status = pipe(from_yices);
  assert(status == 0);
  

  start_solver(Z3, fileno(z3file), from_z3[1]);
  start_solver(YICES, fileno(yicesfile), from_yices[1]);

  assert(z3file != NULL);
  assert(yicesfile != NULL);

  fclose(z3file);
  fclose(yicesfile);

  //Set up our in process sockets

  context = zmq_ctx_new ();
  void *responder = zmq_socket (context, ZMQ_SUB);
  int rc = zmq_bind (responder, "inproc://controller");

  assert (rc == 0);
  
  //Set to receive all messages
  int sk = zmq_setsockopt (responder, ZMQ_SUBSCRIBE, NULL, 0);
  assert (sk == 0);
  
  void *skz3 = zmq_socket(context, ZMQ_PUB);
  rc = zmq_connect(skz3, "inproc://controller");
  
  assert (rc == 0);

  void *skyices = zmq_socket(context, ZMQ_PUB);
  rc = zmq_connect(skyices, "inproc://controller");

  assert (rc == 0);

  //Start the controller / worker threads
  pthread_t control;
  
  status = 
    pthread_create(&control, NULL, control_worker, (void*)responder);

  assert(status == 0);

  start_worker(Z3, skz3, from_z3[0]);
  start_worker(YICES, skyices, from_yices[0]);
  
  while(1)
    sched_yield();
  
  return 0;
}
