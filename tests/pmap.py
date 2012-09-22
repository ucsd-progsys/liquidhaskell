import itertools as it
import threading, Queue

class PMapWorker (threading.Thread):
    def __init__ (self, f, q):
        threading.Thread.__init__ (self)
        self.results = list ()
        self.f       = f
        self.q       = q

    def run(self):
        while True:
            try:
                x = self.q.get_nowait ()
                self.results.append (self.f (x))
                self.q.task_done ()
            except Queue.Empty:
                return

def map (threadcount, f, xs):
    q = Queue.Queue ()
    for x in xs:
        q.put (x)

    workers = [PMapWorker (f, q) for i in range (0, threadcount)]
    for worker in workers:
        worker.start ()
    q.join ()

    return it.chain (*[worker.results for worker in workers])
