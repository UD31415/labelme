'''
Object Detector Manager
Usage :
    from ObjectDetector import ObjectDetector
    d = ObjectDetector("string to you file")
    d.Test()

How to train:
   d = ObjectDetector("string to you file")
   d.Test()

   1. use 'spacebar' to pause and select the object of interest
   2. press 'spacebar' again and observe PSR of the object. if it follows below 10 press 'a'
   3. repeat it for all object appearences that you want to remember
   4. press 's' to save the data

How to test:
   d = ObjectDetector("string to you file")
   d.Test()

   1. use 'spacebar' to pause
   2. 'r' to reload object data
   3. press 'spacebar' to resume tracking
   4. observe 'psr'

-----------------------------
 Ver	Date	 Who	Descr
-----------------------------
0103   31.05.20  UD     Adding clear function
0102   05.03.20  UD     Created
0101   16.02.20  UD     Created
-----------------------------

'''
# Python 2/3 compatibility
#from __future__ import print_function
import sys

import numpy as np
import cv2 as cv
#from .common import RectSelector
#from . import video
#%% Helpers

def draw_str(dst, target, s):
    x, y = target
    cv.putText(dst, s, (x+1, y+1), cv.FONT_HERSHEY_PLAIN, 1.0, (0, 0, 0), thickness = 2, lineType=cv.LINE_AA)
    cv.putText(dst, s, (x, y), cv.FONT_HERSHEY_PLAIN, 1.0, (255, 255, 255), lineType=cv.LINE_AA)

class RectSelector:
    def __init__(self, win, callback):
        self.win = win
        self.callback = callback
        cv.setMouseCallback(win, self.onmouse)
        self.drag_start = None
        self.drag_rect = None
    def onmouse(self, event, x, y, flags, param):
        x, y = np.int16([x, y]) # BUG
        if event == cv.EVENT_LBUTTONDOWN:
            self.drag_start = (x, y)
            return
        if self.drag_start:
            if flags & cv.EVENT_FLAG_LBUTTON:
                xo, yo = self.drag_start
                x0, y0 = np.minimum([xo, yo], [x, y])
                x1, y1 = np.maximum([xo, yo], [x, y])
                self.drag_rect = None
                if x1-x0 > 0 and y1-y0 > 0:
                    self.drag_rect = (x0, y0, x1, y1)
            else:
                rect = self.drag_rect
                self.drag_start = None
                self.drag_rect = None
                if rect:
                    self.callback(rect)
    def draw(self, vis):
        if not self.drag_rect:
            return False
        x0, y0, x1, y1 = self.drag_rect
        cv.rectangle(vis, (x0, y0), (x1, y1), (0, 255, 0), 2)
        return True
    @property
    def dragging(self):
        return self.drag_rect is not None


def rnd_warp(a):
    h, w = a.shape[:2]
    T = np.zeros((2, 3))
    coef = 0.2
    ang = (np.random.rand()-0.5)*coef
    scl = 1+(np.random.rand()-0.5)*coef
    c, s = np.cos(ang)*scl, np.sin(ang)*scl
    T[:2, :2] = [[c,-s], [s, c]]
    # T[:2, :2] += (np.random.rand(2, 2) - 0.5)*coef
    c = (w/2, h/2)
    T[:,2] = c - np.dot(T[:2, :2], c)
    return cv.warpAffine(a, T, (w, h), borderMode = cv.BORDER_REFLECT)

def divSpec(A, B):
    Ar, Ai = A[...,0], A[...,1]
    Br, Bi = B[...,0], B[...,1]
    C = (Ar+1j*Ai)/(Br+1j*Bi)
    C = np.dstack([np.real(C), np.imag(C)]).copy()
    return C

eps = 1e-5

#%% Trackers

class CSRT:
    def __init__(self, frame, rect):
        x, y, w, h = rect
        self.pos = (x, y)
        self.size = (w,h)
        x1, x2 = map(lambda i: max(i, 0) , int(x - w/2), int(x + w/2))
        y1, y2 = map(lambda i: max(i, 0) , int(y - h/2), int(y + h/2))
        frame_gray = cv.cvtColor(frame, cv.COLOR_BGR2GRAY)
        self.tracker = cv.TrackerCSRT_create()
        self.tracker.init(frame_gray, (x1, y1, x2, y2))

    def update(self, frame):
        frame_gray = cv.cvtColor(frame, cv.COLOR_BGR2GRAY)
        (success, box) = self.tracker.update(frame_gray)
        print(box)
        if success:

            (x1, y1, x2, y2) = [float(v) for v in box]
            self.pos = (x1 + self.size[0]/2, y1 + self.size[0]/2)
        return self.pos, success



class MOSSE:
    def __init__(self, frame, rect, gui = False):
        "gui has different rectangle"
        if gui:
            x1, y1, x2, y2  = rect
            w, h        = map(cv.getOptimalDFTSize, [x2-x1, y2-y1]) #w is optimal dft size for width of rect
            x1, y1      = (x1+x2-w)//2, (y1+y2-h)//2
            self.pos    = x, y = x1+0.5*(w-1), y1+0.5*(h-1)
            self.size   = w, h
        else:
            x, y, w, h  = rect
            w,h         = map(cv.getOptimalDFTSize, [w,h])
            self.pos    = x, y
            self.size   = w, h

        frame_gray = cv.cvtColor(frame, cv.COLOR_BGR2GRAY)
        img         = cv.getRectSubPix(frame_gray, (w, h), (x, y))
        self.orig_img = img

        self.win    = cv.createHanningWindow((w, h), cv.CV_32F)
        g           = np.zeros((h, w), np.float32)
        g[h//2, w//2] = 1
        g           = cv.GaussianBlur(g, (-1, -1), 2.0)
        g /= g.max()

        self.G      = cv.dft(g, flags=cv.DFT_COMPLEX_OUTPUT)
        self.H1     = np.zeros_like(self.G)
        self.H2     = np.zeros_like(self.G)
        for _i in range(128):
            b = rnd_warp(img)
            a = self.preprocess(b)
            A = cv.dft(a, flags=cv.DFT_COMPLEX_OUTPUT)
            self.H1 += cv.mulSpectrums(self.G, A, 0, conjB=True)
            self.H2 += cv.mulSpectrums(     A, A, 0, conjB=True)
        self.update_kernel()
        self.update(frame_gray)

    def update(self, frame, rate = 0.125):
        (x, y), (w, h) = self.pos, self.size
        if len(frame.shape)>2:
            frame_gray = cv.cvtColor(frame, cv.COLOR_BGR2GRAY)
        else:
            frame_gray = frame

        self.last_img = img = cv.getRectSubPix(frame_gray, (w, h), (x, y))
        img = self.preprocess(img)
        self.last_resp, (dx, dy), self.psr = self.correlate(img)
        self.good = self.psr > 8.0
        #if not self.good:
        #    return 0,0
        if rate < 0.01:
            return dx,dy,self.psr

        self.pos = (x+dx, y+dy)
        self.last_img = img = cv.getRectSubPix(frame_gray, (w, h), self.pos)
        img     = self.preprocess(img)

        A       = cv.dft(img, flags=cv.DFT_COMPLEX_OUTPUT)
        H1      = cv.mulSpectrums(self.G, A, 0, conjB=True)
        H2      = cv.mulSpectrums(     A, A, 0, conjB=True)
        self.H1 = self.H1 * (1.0-rate) + H1 * rate
        self.H2 = self.H2 * (1.0-rate) + H2 * rate
        self.update_kernel()
        return self.pos[0],self.pos[1],self.psr


    @property
    def state_vis(self):
        f       = cv.idft(self.H, flags=cv.DFT_SCALE | cv.DFT_REAL_OUTPUT )
        h, w    = f.shape
        f       = np.roll(f, -h//2, 0)
        f       = np.roll(f, -w//2, 1)
        kernel  = np.uint8( (f-f.min()) / np.ptp(f)*255 )
        kernel  = self.orig_img
        resp    = self.last_resp
        resp    = np.uint8(np.clip(resp/resp.max(), 0, 1)*255)
        draw_str(resp, (2, 2+16), 'PSR: %.2f' % self.psr)
        vis     = np.hstack([self.last_img, kernel, resp])
        return vis

    def draw_state(self, vis):
        (x, y), (w, h) = self.pos, self.size
        x1, y1, x2, y2 = int(x-0.5*w), int(y-0.5*h), int(x+0.5*w), int(y+0.5*h)
        cv.rectangle(vis, (x1, y1), (x2, y2), (0, 0, 255))
        if self.good:
            cv.circle(vis, (int(x), int(y)), 2, (0, 0, 255), -1)
        else:
            cv.line(vis, (x1, y1), (x2, y2), (0, 0, 255))
            cv.line(vis, (x2, y1), (x1, y2), (0, 0, 255))
        #draw_str(vis, (x1, y2+16), 'PSR: %.2f' % self.psr)

    def preprocess(self, img):
        img = np.log(np.float32(img)+1.0)
        img = (img-img.mean()) / (img.std()+eps)
        return img*self.win

    def correlate(self, img):
        C = cv.mulSpectrums(cv.dft(img, flags=cv.DFT_COMPLEX_OUTPUT), self.H, 0, conjB=True)
        resp = cv.idft(C, flags=cv.DFT_SCALE | cv.DFT_REAL_OUTPUT)
        h, w = resp.shape
        _, mval, _, (mx, my) = cv.minMaxLoc(resp)
        side_resp = resp.copy()
        cv.rectangle(side_resp, (mx-5, my-5), (mx+5, my+5), 0, -1)
        smean, sstd = side_resp.mean(), side_resp.std()
        psr = (mval-smean) / (sstd+eps)
        return resp, (mx-w//2, my-h//2), psr

    def update_kernel(self):
        self.H = divSpec(self.H1, self.H2)
        self.H[...,1] *= -1

class ObjectDetector:
    def __init__(self):
        self.cap      = []
        self.frame    = []
        self.rect_sel = []
        self.trackers = []
        self.paused   = True
        self.update_rate = 0

    def Init(self, video_src='0', img_size = (640,480)):
        self.cap        = cv.VideoCapture(video_src)
        w, h            = img_size
        self.frame      = np.zeros((w,h),dtype=np.uint8)  
        self.cap.set(cv.CAP_PROP_FRAME_WIDTH, w)
        self.cap.set(cv.CAP_PROP_FRAME_HEIGHT, h)        
        self.getFrame()
        #_, self.frame = self.cap.read()
        cv.imshow('frame', self.frame)
        self.rect_sel   = RectSelector('frame', self.onrect)
        self.trackers   = []
        self.paused     = False

        print('Detector is initialized')


    def onrect(self, rect):
        #frame_gray = cv.cvtColor(self.frame, cv.COLOR_BGR2GRAY)
        frame_color = self.frame
        tracker = MOSSE(frame_color, rect, gui=True)
        self.trackers.append(tracker)
        print('New track added')

        # check if some one already is tracking this
#        isTracked = False
#        for tracker in self.trackers:
#            x,y = tracker.update(frame_gray,0)
#            isTracked = isTracked or tracker.good
#
#        if not isTracked:
#            tracker = MOSSE(frame_gray, rect)
#            self.trackers.append(tracker)
#        else:
#            print('This region is tracked already')

    def getFrame(self):
        # show visual info
        #rect_crop   = [880, 650, 320, 240] # single hole
        #rect_crop   = [680, 450, 720, 640] # single hole
        ret = True
        if not self.cap.isOpened():
            return False
        
        if self.paused:
            return True
        
        ret, frame = self.cap.read()
        if ret:
                #self.frame  = frame[int(rect_crop[1]):int(rect_crop[1]+rect_crop[3]), int(rect_crop[0]):int(rect_crop[0]+rect_crop[2])]
                #self.frame  = frame[int(rect_crop[1]):int(rect_crop[1]+rect_crop[3]), int(rect_crop[0]):int(rect_crop[0]+rect_crop[2])]
            self.frame  = frame
        return ret


    def detect(self, frame, rate = 0.0):
        # show visual info
        frame_gray  = cv.cvtColor(frame, cv.COLOR_BGR2GRAY)
        x,y,psr = 0,0,0
        for tracker in self.trackers:
            x_temp,y_temp,psr_temp = tracker.update(frame_gray, rate)
            if psr_temp > psr:
                x,y,psr = x_temp,y_temp,psr_temp

        return x,y,psr

    def show(self, frame, x,y,psr):
        # show visual info
        i, dx, dy, y0 = 0, 20 , 35, 20
        fs, ft, fc, ff = 0.6, 2, (240,220,10),  cv.FONT_HERSHEY_SIMPLEX

        for tracker in self.trackers:
            tracker.draw_state(frame)

        #if len(self.trackers) > 0:
        #    cv.imshow('tracker state', self.trackers[-1].state_vis)
        for k in range(len(self.trackers)):
            cv.imshow(str(k)+' tracker state', self.trackers[k].state_vis)


        self.rect_sel.draw(frame)

        i = 1; cv.putText(frame ,'Y = {0: 4.1f}'.format(y),  tuple([dx,i*dy+y0]), ff, fs,(0,0,255),ft,cv.LINE_AA)
        i = 2; cv.putText(frame ,'X = {0: 4.1f}'.format(x),  tuple([dx,i*dy+y0]), ff, fs,(0,255,0),ft,cv.LINE_AA)
        i = 3; cv.putText(frame ,'P = {0: 4.1f}'.format(psr),tuple([dx,i*dy+y0]), ff, fs,(255,255,0),ft,cv.LINE_AA)
        cv.imshow('frame', frame)

    def clear(self):
        # show visual info
        for k in range(len(self.trackers)):
            cv.destroyWindow(str(k)+' tracker state')

        self.trackers = []

    def save(self):
        # saves trackeras to file
        fname = 'Trackers.npz'
        values_array       = self.trackers
        np.savez(fname,values = values_array)
        print('saving file '+ fname)

    def load(self):
        # load trackeras from file
        fname = 'Trackers.npz'
        load = np.load(fname, allow_pickle = True)
        self.trackers = load['values']
        print('loading file '+ fname)

    def Test(self):

        while True:

            ret = self.getFrame()
            if not ret:
                break

            # detect using the latest info
            x,y,psr = self.detect(self.frame, self.update_rate)

            # show the info
            vis = self.frame.copy()
            self.show(vis,x,y,psr)

            # user interaction
            ch = cv.waitKey(50)
            if ch == 27:
                break
            if ch == ord(' '):
                self.paused = not self.paused
            if ch == ord('c'):
                self.clear()

            if ch == ord('s'):
                self.save()
            if ch == ord('r'):
                self.load()
            if ch == ord('u'):  # update trackers
                self.update_rate = 0.2 if self.update_rate < 0.1 else 0
                print(f'Update rate {self.update_rate}')
            if ch == ord('a'):  # update trackers
                if len(self.trackers) > 0:
                    ul = np.array(self.trackers[-1].pos)
                    sz = np.array(self.trackers[-1].size)/2
                    rect = tuple(np.int16(ul-sz)) + tuple(np.int16(ul+sz))
                    self.onrect(rect)



        self.cap.release()
        cv.destroyAllWindows()

if __name__ == '__main__':
    print (__doc__)
    import sys, getopt
    opts, args = getopt.getopt(sys.argv[1:], '', ['pause'])
    opts = dict(opts)
    #try:
    #video_src = args[0]
    # RobotA
    video_src = r'D:\Uri\HamLet\Customers\Primatic\Data\2019-12-31\Test1.avi'
    # brown box
    #video_src = r'D:\Uri\Data\Videos\Hamlet\BrownBox\WIN_20190904_17_01_33_Pro.mp4'
    # with plastic in holes
    #video_src = r'D:\Uri\HamLet\Customers\Primatic\Data\2020-02-02\SideWithTubes.avi'
   # gum box
    #video_src = r'D:\Uri\Data\Videos\Robi\Objects\WIN_20181115_19_29_04_Pro.mp4'

#except:
    video_src = 0

    d = ObjectDetector()
    d.Init(video_src)
    d.Test()
