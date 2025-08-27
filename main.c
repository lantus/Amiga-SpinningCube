#include "support/gcc8_c_support.h"
#include <exec/types.h>
#include <exec/exec.h>
#include <graphics/gfx.h>
#include <graphics/gfxbase.h>
#include <hardware/custom.h>
#include <hardware/intbits.h>
#include <proto/exec.h>
#include <proto/graphics.h>
#include <proto/dos.h>

// Global variables
struct ExecBase *SysBase;
volatile struct Custom *custom;
struct DosLibrary *DOSBase;
struct GfxBase *GfxBase = NULL;
struct ViewPort *viewPort = NULL;
struct RasInfo rasInfo;
struct BitMap *bitMap = NULL;
UWORD *copperPtr = NULL;

static UWORD SystemInts;
static UWORD SystemDMA;
static UWORD SystemADKCON;
static volatile APTR VBR = 0;
static APTR SystemIrq;
struct View *ActiView;

extern __attribute__((aligned(2))) const SHORT SinTable[1024];
extern __attribute__((aligned(2))) const SHORT CosTable[1024];

#define SCREEN_WIDTH 320
#define SCREEN_HEIGHT 256
#define BPL_DEPTH 1
#define BPL_SIZE (SCREEN_WIDTH * SCREEN_HEIGHT / 8) // Bytes per bitplane
#define NUM_COLORS (1 << BPL_DEPTH)

/* write definitions for dmaconw */
#define DMAF_SETCLR  0x8000
#define DMAF_AUDIO   0x000F   /* 4 bit mask */
#define DMAF_AUD0    0x0001
#define DMAF_AUD1    0x0002
#define DMAF_AUD2    0x0004
#define DMAF_AUD3    0x0008
#define DMAF_DISK    0x0010
#define DMAF_SPRITE  0x0020
#define DMAF_BLITTER 0x0040
#define DMAF_COPPER  0x0080
#define DMAF_RASTER  0x0100
#define DMAF_MASTER  0x0200
#define DMAF_BLITHOG 0x0400
#define DMAF_ALL     0x01FF   /* all dma channels */

#define abs(x) ((x) > 0 ? (x) : -(x)) 

// Global variables
UBYTE *bitplanes1 = NULL;
UBYTE *bitplanes2 = NULL;
UBYTE *frontBuffer = NULL;
UBYTE *backBuffer = NULL;
UWORD *copperList = NULL;
struct Interrupt vblankInt;
BOOL running = TRUE;

// Consts for 3D Cube
 
WORD ax = 0;
WORD ay = 0;
WORD az = 0;

const UBYTE center_x = SCREEN_WIDTH >> 1;
const UBYTE center_y = SCREEN_HEIGHT >> 1;
const WORD centre_z = SCREEN_HEIGHT * 8;

// 3D point structure
typedef struct 
{
    BYTE x, y, z;
} Vec3;

// 2D point structure
typedef struct 
{
    BYTE x, y;
} Vec2;

// Cube vertices (centered at origin, edge length 2)
Vec3 cube_vertices[8] = 
{
    {-1, -1, -1}, {1, -1, -1}, {1, 1, -1}, {-1, 1, -1}, // Front face
    {-1, -1, 1},  {1, -1, 1},  {1, 1, 1},  {-1, 1, 1}   // Back face
};
 
__attribute__((always_inline)) inline short MouseLeft() { return !((*(volatile UBYTE*)0xbfe001) & 64); }
__attribute__((always_inline)) inline short MouseRight() { return !((*(volatile UWORD*)0xdff016) & (1 << 10)); }
 

// set up a 320x256 lowres display
__attribute__((always_inline)) inline USHORT* screenScanDefault(USHORT* copListEnd) 
{
	const USHORT x=129;
	const USHORT width=320;
	const USHORT height=256;
	const USHORT y=44;
	const USHORT RES=8; //8=lowres,4=hires
	USHORT xstop = x+width;
	USHORT ystop = y+height;
	USHORT fw=(x>>1)-RES;

	*copListEnd++ = offsetof(struct Custom, ddfstrt);
	*copListEnd++ = fw;
	*copListEnd++ = offsetof(struct Custom, ddfstop);
	*copListEnd++ = fw+(((width>>4)-1)<<3);
	*copListEnd++ = offsetof(struct Custom, diwstrt);
	*copListEnd++ = x+(y<<8);
	*copListEnd++ = offsetof(struct Custom, diwstop);
	*copListEnd++ = (xstop-256)+((ystop-256)<<8);
	return copListEnd;
}

__attribute__((always_inline)) inline USHORT* copSetPlanes(UBYTE bplPtrStart,USHORT* copListEnd,const UBYTE **planes,int numPlanes) {
	for (USHORT i=0;i<numPlanes;i++) {
		ULONG addr=(ULONG)planes[i];
		*copListEnd++=offsetof(struct Custom, bplpt[0]) + (i + bplPtrStart) * sizeof(APTR);
		*copListEnd++=(UWORD)(addr>>16);
		*copListEnd++=offsetof(struct Custom, bplpt[0]) + (i + bplPtrStart) * sizeof(APTR) + 2;
		*copListEnd++=(UWORD)addr;
	}
	return copListEnd;
}

__attribute__((always_inline)) inline USHORT* copSetColor(USHORT* copListCurrent,USHORT index,USHORT color) {
	*copListCurrent++=offsetof(struct Custom, color) + sizeof(UWORD) * index;
	*copListCurrent++=color;
	return copListCurrent;
}

void WaitLine(USHORT line) 
{
	while (1) 
    {
		volatile ULONG vpos=*(volatile ULONG*)0xDFF004;
		if(((vpos >> 8) & 511) == line)
			break;
	}
}

static APTR GetVBR(void) {
    APTR vbr = 0;
    UWORD getvbr[] = { 0x4e7a, 0x0801, 0x4e73 }; // MOVEC.L VBR,D0 RTE
    if (SysBase->AttnFlags & AFF_68010)
        vbr = (APTR)Supervisor((ULONG (*)())getvbr);
    return vbr;
}

void SetInterruptHandler(APTR interrupt) {
    *(volatile APTR*)(((UBYTE*)VBR) + 0x6c) = interrupt;
}

APTR GetInterruptHandler() {
    return *(volatile APTR*)(((UBYTE*)VBR) + 0x6c);
}

void WaitVbl() {
    while (1) {
        volatile ULONG vpos = *(volatile ULONG*)0xdff004;
        vpos &= 0x1ff00;
        if (vpos != (311 << 8)) break;
    }
    while (1) {
        volatile ULONG vpos = *(volatile ULONG*)0xdff004;
        vpos &= 0x1ff00;
        if (vpos == (311 << 8)) break;
    }
}
 
void TakeSystem() 
{
	Forbid();

	//Save current interrupts and DMA settings so we can restore them upon exit. 
	SystemADKCON=custom->adkconr;
	SystemInts=custom->intenar;
	SystemDMA=custom->dmaconr;
	ActiView=GfxBase->ActiView; //store current view

	LoadView(0);
	WaitTOF();
	WaitTOF();

	WaitVbl();
	WaitVbl();

	OwnBlitter();
	WaitBlit();	
	Disable();
	
	custom->intena=0x7fff;//disable all interrupts
	custom->intreq=0x7fff;//Clear any interrupts that were pending
	
	custom->dmacon=0x7fff;//Clear all DMA channels

	//set all colors black
	for(int a=0;a<32;a++)
		custom->color[a]=0;

	WaitVbl();
	WaitVbl();

	VBR=GetVBR();
	SystemIrq=GetInterruptHandler(); //store interrupt register
}

void FreeSystem()
{ 
	WaitVbl();
	WaitBlit();
    
	custom->intena=0x7fff;//disable all interrupts
	custom->intreq=0x7fff;//Clear any interrupts that were pending
	custom->dmacon=0x7fff;//Clear all DMA channels

	//restore interrupts
	SetInterruptHandler(SystemIrq);

	/*Restore system copper list(s). */
	custom->cop1lc=(ULONG)GfxBase->copinit;
	custom->cop2lc=(ULONG)GfxBase->LOFlist;
	custom->copjmp1=0x7fff; //start coppper

	/*Restore all interrupts and DMA settings. */
	custom->intena=SystemInts|0x8000;
	custom->dmacon=SystemDMA|0x8000;
	custom->adkcon=SystemADKCON|0x8000;

	WaitBlit();	
	DisownBlitter();
	Enable();

	LoadView(ActiView);
	WaitTOF();
	WaitTOF();

	Permit();
} 
 
/* Draw line (Bresenham, CPU-based) */
__attribute__((always_inline)) inline  void DrawLineCPU(int x0, int y0, int x1, int y1) 
{

    SHORT dx = abs(x1 - x0), dy = abs(y1 - y0);
    SHORT sx = x0 < x1 ? 1 : -1, sy = y0 < y1 ? 1 : -1;
    SHORT err = dx - dy;
    UBYTE *bpl = (UBYTE *)backBuffer + (y0 * 40) + (x0 >> 3);
    UBYTE bit = 0x80 >> (x0 & 7);

    while (1) 
    {
        *bpl |= bit; /* Set pixel */
        if (x0 == x1 && y0 == y1) break;
        
        SHORT e2 = err << 1;
        
        if (e2 > -dy) 
        {
            err -= dy;
            x0 += sx;   
        }
        if (e2 < dx) 
        {
            err += dx;
            y0 += sy;
        }

        bpl = (UBYTE *)backBuffer + (y0 * 40) + (x0 >> 3);
        bit = 0x80 >> (x0 & 7);
    }
}

void DrawLineBliter(int x0, int y0, int x1, int y1) 
{
    if (x0 < 0 || x0 >= SCREEN_WIDTH || y0 < 0 || y0 >= SCREEN_HEIGHT ||
        x1 < 0 || x1 >= SCREEN_WIDTH || y1 < 0 || y1 >= SCREEN_HEIGHT) return;

    int dx = x1 - x0, dy = y1 - y0;
    int steps = abs(dx) > abs(dy) ? abs(dx) : abs(dy);
    int xinc = dx / (float)steps;
    int yinc = dy / (float)steps;

    // Simplify for horizontal/vertical lines first
    if (dy == 0) { // Horizontal line
        int xstart = x0 < x1 ? x0 : x1;
        int xend = x0 < x1 ? x1 : x0;
        int byteOffset = y0 * 40 + (xstart >> 3);
        UWORD shift = 0x8000 >> (xstart & 7);
        UWORD mask = (0xFFFF >> (15 - (xend & 7))) & (0xFFFF << (xstart & 7));

        WaitBlit();
        custom->bltcon0 = 0x0F00 | ((xstart & 7) << 12); // Minterm, shift
        custom->bltcon1 = 0x0000;
        custom->bltafwm = 0xFFFF;
        custom->bltalwm = mask;
        custom->bltapt = (APTR)&shift; // A channel as initial pixel
        custom->bltdpt = (APTR)(backBuffer + byteOffset);
        custom->bltamod = 0;
        custom->bltdmod = 40 - ((xend - xstart + 7) >> 3); // Adjust modulo
        custom->bltsize = (1 << 6) | ((xend - xstart + 7) >> 3); // Height 1, width in words
    } else if (dx == 0) { // Vertical line
        int ystart = y0 < y1 ? y0 : y1;
        int yend = y0 < y1 ? y1 : y0;
        int byteOffset = ystart * 40 + (x0 >> 3);
        UWORD shift = 0x8000 >> (x0 & 7);

        WaitBlit();
        custom->bltcon0 = 0x0F00 | ((x0 & 7) << 12); // Minterm, shift
        custom->bltcon1 = 0x0000;
        custom->bltafwm = 0xFFFF;
        custom->bltalwm = 0xFFFF;
        custom->bltapt = (APTR)&shift; // A channel as initial pixel
        custom->bltdpt = (APTR)(backBuffer + byteOffset);
        custom->bltamod = 0;
        custom->bltdmod = 40; // Modulo for vertical movement
        custom->bltsize = ((yend - ystart + 1) << 6) | 1; // Height, width 1 word
    }
    // Diagonal lines require multiple blits; this is a simplification for now
}
 
void PlotPixel(int x, int y) {
    if (x < 0 || x >= SCREEN_WIDTH || y < 0 || y >= SCREEN_HEIGHT) return;
    UBYTE *bpl = (UBYTE *)backBuffer + (y * 40) + (x >> 3); // 40 bytes per line
    UBYTE bit = 0x80 >> (x & 7); // Bit position within byte
    *bpl |= bit; // Set pixel to 1 (white, COLOR01)
}

 
 
void BlitterDrawPixel(int x, int y) 
{
   
    custom->bltcon0 = 0x0F00 | (0x11 << 8); // Minterm and shift
    custom->bltcon1 = 0x0000;
    custom->bltafwm = 0xFFFF;
    custom->bltalwm = 0xFFFF;
    custom->bltapt = (APTR)((ULONG)backBuffer + (y * 40) + (x >> 3));
    custom->bltdpt = (APTR)((ULONG)backBuffer + (y * 40) + (x >> 3));
    custom->bltsize = (1 << 6) | 1; // 1 line, 1 word
    WaitBlit();
}


/* Clear bitplane */
void ClearBitplane(void) 
{
    memclr((UBYTE *)backBuffer, BPL_SIZE * BPL_DEPTH);
}
 
 
static __attribute__((interrupt)) void InterruptHandler() 
{
	custom->intreq=(1<<INTB_VERTB); 
    // Update Copper list to point to new front buffer
    UWORD *copPtr = copperList;
    *copPtr++ = 0x008E; *copPtr++ = 0x2C81;
    *copPtr++ = 0x0090; *copPtr++ = 0x2CC1;
    *copPtr++ = 0x0092; *copPtr++ = 0x0038;
    *copPtr++ = 0x0094; *copPtr++ = 0x00D0;
    *copPtr++ = 0x0100; *copPtr++ = 0x1200;
    *copPtr++ = 0x0108; *copPtr++ = 0x0000;
    *copPtr++ = 0x010A; *copPtr++ = 0x0000;
    ULONG bplAddr = (ULONG)frontBuffer;
    *copPtr++ = 0x00E0; *copPtr++ = bplAddr >> 16;
    *copPtr++ = 0x00E2; *copPtr++ = bplAddr & 0xFFFF;
    *copPtr++ = 0x0180; *copPtr++ = 0x0125;
    *copPtr++ = 0x0182; *copPtr++ = 0x0FFF;
    *copPtr++ = 0xFFFF; *copPtr++ = 0xFFFE;

    custom->cop1lc = (ULONG)copperList; // Set Copper list
    custom->copjmp1 = 0x7fff; // Trigger Copper
 
}

 
void SetupCopper()
{
    // Initialize Copper list
    UWORD *copPtr = copperList;
    
    *copPtr++ = 0x008E; *copPtr++ = 0x2C81; // DIWSTRT
    *copPtr++ = 0x0090; *copPtr++ = 0x2CC1; // DIWSTOP
    *copPtr++ = 0x0092; *copPtr++ = 0x0038; // DDFSTRT
    *copPtr++ = 0x0094; *copPtr++ = 0x00D0; // DDFSTOP
    *copPtr++ = 0x0100; *copPtr++ = 0x1200; // BPLCON0
    *copPtr++ = 0x0108; *copPtr++ = 0x0000; // BPL1MOD
    *copPtr++ = 0x010A; *copPtr++ = 0x0000; // BPL2MOD
    ULONG bplAddr = (ULONG)frontBuffer; // Use front buffer
    *copPtr++ = 0x00E0; *copPtr++ = bplAddr >> 16;
    *copPtr++ = 0x00E2; *copPtr++ = bplAddr & 0xFFFF;
    *copPtr++ = 0x0180; *copPtr++ = 0x0125; // COLOR00
    *copPtr++ = 0x0182; *copPtr++ = 0x0FFF; // COLOR01
    *copPtr++ = 0xFFFF; *copPtr++ = 0xFFFE; // End

    WaitBlit();

}

// Cleanup
void DisableCopper(void)
{
    if (copperList)
    {
        custom->cop1lc = 0; // Disable Copper
        FreeMem(copperList, 1024);
        copperList = NULL;
    }

    if (bitplanes1)
    {
        FreeMem(bitplanes1, BPL_SIZE * BPL_DEPTH);
        bitplanes1 = NULL;
    }
    if (bitplanes2)
    {
        FreeMem(bitplanes2, BPL_SIZE * BPL_DEPTH);
        bitplanes2 = NULL;
    }
    
}

// Render the cube
void RenderCube() 
{
    LONG x,y,z = 0;
    LONG x2 = 0;
    SHORT cax;
    SHORT sax;
    SHORT cay;
    SHORT say;
    SHORT caz;
    SHORT saz;
    SHORT depth;
    USHORT xe1, xe2, xe3, xe4, xe5, xe6, xe7, xe8;
    USHORT ye1, ye2, ye3, ye4, ye5, ye6, ye7, ye8;

    cax = CosTable[ax];
    sax = SinTable[ax];
    cay = CosTable[ay];
    say = SinTable[ay];
    caz = cax;
    saz = sax;

    // Unroll

    // Rotation X
    x =  cube_vertices[0].x<<8;
    y =  cube_vertices[0].y*cax+cube_vertices[0].z*sax;
    z = -cube_vertices[0].y*sax+cube_vertices[0].z*cax;
    // Rotation Y
    x2 =  x*cay+z*say;
    z =  -x*say+z*cay;
    // Rotation Z
    x2 =  x2>>8;
    x = x2*caz+y*saz;
    y = -x2*saz+y*caz;
    // Projection
    depth = centre_z+(z>>8);
    xe1 = center_x+(x/depth);
    ye1 = center_y+(y/depth);

    // Rotation X
    x =  cube_vertices[1].x<<8;
    y =  cube_vertices[1].y*cax+cube_vertices[1].z*sax;
    z = -cube_vertices[1].y*sax+cube_vertices[1].z*cax;
    // Rotation Y
    x2 =  x*cay+z*say;
    z =  -x*say+z*cay;
    // Rotation Z
    x2 =  x2>>8;
    x = x2*caz+y*saz;
    y = -x2*saz+y*caz;
    // Projection
    depth = centre_z+(z>>8);
    xe2 = center_x+(x/depth);
    ye2 = center_y+(y/depth);

    // Rotation X
    x =  cube_vertices[2].x<<8;
    y =  cube_vertices[2].y*cax+cube_vertices[2].z*sax;
    z = -cube_vertices[2].y*sax+cube_vertices[2].z*cax;
    // Rotation Y
    x2 =  x*cay+z*say;
    z =  -x*say+z*cay;
    // Rotation Z
    x2 =  x2>>8;
    x = x2*caz+y*saz;
    y = -x2*saz+y*caz;
    // Projection
    depth = centre_z+(z>>8);
    xe3 = center_x+(x/depth);
    ye3 = center_y+(y/depth);

    // Rotation X
    x =  cube_vertices[3].x<<8;
    y =  cube_vertices[3].y*cax+cube_vertices[3].z*sax;
    z = -cube_vertices[3].y*sax+cube_vertices[3].z*cax;
    // Rotation Y
    x2 =  x*cay+z*say;
    z =  -x*say+z*cay;
    // Rotation Z
    x2 =  x2>>8;
    x = x2*caz+y*saz;
    y = -x2*saz+y*caz;
    // Projection
    depth = centre_z+(z>>8);
    xe4 = center_x+(x/depth);
    ye4 = center_y+(y/depth);

    // Rotation X
    x =  cube_vertices[4].x<<8;
    y =  cube_vertices[4].y*cax+cube_vertices[4].z*sax;
    z = -cube_vertices[4].y*sax+cube_vertices[4].z*cax;
    // Rotation Y
    x2 =  x*cay+z*say;
    z =  -x*say+z*cay;
    // Rotation Z
    x2 =  x2>>8;
    x = x2*caz+y*saz;
    y = -x2*saz+y*caz;
    // Projection
    depth = centre_z+(z>>8);
    xe5 = center_x+(x/depth);
    ye5 = center_y+(y/depth);

    // Rotation X
    x =  cube_vertices[5].x<<8;
    y =  cube_vertices[5].y*cax+cube_vertices[5].z*sax;
    z = -cube_vertices[5].y*sax+cube_vertices[5].z*cax;
    // Rotation Y
    x2 =  x*cay+z*say;
    z =  -x*say+z*cay;
    // Rotation Z
    x2 =  x2>>8;
    x = x2*caz+y*saz;
    y = -x2*saz+y*caz;
    // Projection
    depth = centre_z+(z>>8);
    xe6 = center_x+(x/depth);
    ye6 = center_y+(y/depth);

    // Rotation X
    x =  cube_vertices[6].x<<8;
    y =  cube_vertices[6].y*cax+cube_vertices[6].z*sax;
    z = -cube_vertices[6].y*sax+cube_vertices[6].z*cax;
    // Rotation Y
    x2 =  x*cay+z*say;
    z =  -x*say+z*cay;
    // Rotation Z
    x2 =  x2>>8;
    x = x2*caz+y*saz;
    y = -x2*saz+y*caz;
    // Projection
    depth = centre_z+(z>>8);
    xe7 = center_x+(x/depth);
    ye7 = center_y+(y/depth);

    // Rotation X
    x =  cube_vertices[7].x<<8;
    y =  cube_vertices[7].y*cax+cube_vertices[7].z*sax;
    z = -cube_vertices[7].y*sax+cube_vertices[7].z*cax;
    // Rotation Y
    x2 =  x*cay+z*say;
    z =  -x*say+z*cay;
    // Rotation Z
    x2 =  x2>>8;
    x = x2*caz+y*saz;
    y = -x2*saz+y*caz;
    // Projection
    depth = centre_z+(z>>8);
    xe8 = center_x+(x/depth);
    ye8 = center_y+(y/depth);

    DrawLineCPU(xe2, ye2, xe6, ye6);
    DrawLineCPU(xe6, ye6, xe5, ye5);
    DrawLineCPU(xe5, ye5, xe1, ye1);
    DrawLineCPU(xe1, ye1, xe2, ye2);
    DrawLineCPU(xe5, ye5, xe8, ye8);
    DrawLineCPU(xe8, ye8, xe7, ye7);
    DrawLineCPU(xe7, ye7, xe6, ye6);
    DrawLineCPU(xe1, ye1, xe4, ye4);
    DrawLineCPU(xe4, ye4, xe3, ye3);
    DrawLineCPU(xe3, ye3, xe2, ye2);
    DrawLineCPU(xe3, ye3, xe7, ye7);
    DrawLineCPU(xe8, ye8, xe4, ye4);
}

int main(void)
{

    SysBase = *((struct ExecBase**)4UL);
	custom = (struct Custom*)0xdff000;

    // Allocate CHIP RAM for bitplanes
 
    bitplanes1 = AllocMem(BPL_SIZE * BPL_DEPTH, MEMF_CHIP | MEMF_CLEAR);
    bitplanes2 = AllocMem(BPL_SIZE * BPL_DEPTH, MEMF_CHIP | MEMF_CLEAR);
    
    if (!bitplanes1 || !bitplanes2) {
        if (bitplanes1) FreeMem(bitplanes1, BPL_SIZE * BPL_DEPTH);
        if (bitplanes2) FreeMem(bitplanes2, BPL_SIZE * BPL_DEPTH);
        Exit(0);
    }

    // Initialize front and back buffers
    frontBuffer = bitplanes1;
    backBuffer = bitplanes2;
   
    // Allocate CHIP RAM for Copper list
    copperList = AllocMem(1024, MEMF_CHIP | MEMF_CLEAR);
     
	// We will use the graphics library only to locate and restore the system copper list once we are through.

	GfxBase = (struct GfxBase *)OpenLibrary((CONST_STRPTR)"graphics.library",0);
	if (!GfxBase)
		Exit(0);

	// used for printing
	DOSBase = (struct DosLibrary*)OpenLibrary((CONST_STRPTR)"dos.library", 0);
	if (!DOSBase)
		Exit(0);
 
    Delay(10);

	TakeSystem();

	WaitVbl();
 
    SetupCopper();
 
    custom->cop1lc = (ULONG)copperList; // Set Copper list

    WaitVbl();

	custom->dmacon = DMAF_BLITTER; //disable blitter dma for copjmp bug
	custom->copjmp1 = 0x7fff; //start coppper
	custom->dmacon = DMAF_SETCLR | DMAF_MASTER | DMAF_RASTER | DMAF_COPPER;
 
    SetInterruptHandler((APTR)InterruptHandler);
 
    custom->intena = INTF_SETCLR | INTF_INTEN | INTF_VERTB;
    custom->intreq=(1<<INTB_VERTB);//reset vbl req

	while(!MouseLeft()) 
    {	
        
        ClearBitplane(); // Clears backBuffer

        ax = (ax - 4) & 1023; // Faster rotation around X-axis
        ay = (ay + 4) & 1023; // Faster rotation around Y-axis
        az = (az - 4) & 1023; // Faster rotation around Z-axis

        RenderCube(); // Draws to backBuffer

        WaitVbl(); // Wait for vertical blank

        // Swap buffers
        UBYTE *temp = frontBuffer;
        frontBuffer = backBuffer;
        backBuffer = temp;
	}

    DisableCopper();
    FreeSystem();

    return 0;
}