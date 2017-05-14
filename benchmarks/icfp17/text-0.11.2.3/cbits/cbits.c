/*
 * Copyright (c) 2011 Bryan O'Sullivan <bos@serpentine.com>.
 *
 * Portions copyright (c) 2008-2010 Björn Höhrmann <bjoern@hoehrmann.de>.
 *
 * See http://bjoern.hoehrmann.de/utf-8/decoder/dfa/ for details.
 */

#include <string.h>
#include <stdint.h>
#include <stdio.h>

void _hs_text_memcpy(void *dest, size_t doff, const void *src, size_t soff,
		     size_t n)
{
  memcpy(dest + (doff<<1), src + (soff<<1), n<<1);
}

int _hs_text_memcmp(const void *a, size_t aoff, const void *b, size_t boff,
		    size_t n)
{
  return memcmp(a + (aoff<<1), b + (boff<<1), n<<1);
}

#define UTF8_ACCEPT 0
#define UTF8_REJECT 12

static const uint8_t utf8d[] = {
  /*
   * The first part of the table maps bytes to character classes that
   * to reduce the size of the transition table and create bitmasks.
   */
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,  9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,
   7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,  7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,
   8,8,2,2,2,2,2,2,2,2,2,2,2,2,2,2,  2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
  10,3,3,3,3,3,3,3,3,3,3,3,3,4,3,3, 11,6,6,6,5,8,8,8,8,8,8,8,8,8,8,8,

  /*
   * The second part is a transition table that maps a combination of
   * a state of the automaton and a character class to a state.
   */
   0,12,24,36,60,96,84,12,12,12,48,72, 12,12,12,12,12,12,12,12,12,12,12,12,
  12, 0,12,12,12,12,12, 0,12, 0,12,12, 12,24,12,12,12,12,12,24,12,24,12,12,
  12,12,12,12,12,12,12,24,12,12,12,12, 12,24,12,12,12,12,12,12,12,24,12,12,
  12,12,12,12,12,12,12,36,12,36,12,12, 12,36,12,12,12,12,12,36,12,36,12,12,
  12,36,12,12,12,12,12,12,12,12,12,12,
};

static inline uint32_t
decode(uint32_t *state, uint32_t* codep, uint32_t byte) {
  uint32_t type = utf8d[byte];

  *codep = (*state != UTF8_ACCEPT) ?
    (byte & 0x3fu) | (*codep << 6) :
    (0xff >> type) & (byte);

  return *state = utf8d[256 + *state + type];
}

/*
 * A best-effort decoder. Runs until it hits either end of input or
 * the start of an invalid byte sequence.
 *
 * At exit, updates *destoff with the next offset to write to, and
 * returns the next source offset to read from.
 */
uint8_t const *
_hs_text_decode_utf8(uint16_t *dest, size_t *destoff,
		     const uint8_t const *src, const uint8_t const *srcend)
{
  uint16_t *d = dest + *destoff;
  const uint8_t const *s = src;
  uint32_t state = UTF8_ACCEPT;

  while (s < srcend) {
    uint32_t codepoint;

#if defined(__i386__) || defined(__x86_64__)
    /*
     * This code will only work on a little-endian system that
     * supports unaligned loads.
     *
     * It gives a substantial speed win on data that is purely or
     * partly ASCII (e.g. HTML), at only a slight cost on purely
     * non-ASCII text.
     */

    if (state == UTF8_ACCEPT) {
      while (s < srcend - 4) {
	codepoint = *((uint32_t *) s);
	if ((codepoint & 0x80808080) != 0)
	  break;
	s += 4;

	/*
	 * Tried 32-bit stores here, but the extra bit-twiddling
	 * slowed the code down.
	 */

	*d++ = (uint16_t) (codepoint & 0xff);
	*d++ = (uint16_t) ((codepoint >> 8) & 0xff);
	*d++ = (uint16_t) ((codepoint >> 16) & 0xff);
	*d++ = (uint16_t) ((codepoint >> 24) & 0xff);
      }
    }
#endif

    if (decode(&state, &codepoint, *s++) != UTF8_ACCEPT) {
      if (state != UTF8_REJECT)
	continue;
      break;
    }

    if (codepoint <= 0xffff)
      *d++ = (uint16_t) codepoint;
    else {
      *d++ = (uint16_t) (0xD7C0 + (codepoint >> 10));
      *d++ = (uint16_t) (0xDC00 + (codepoint & 0x3FF));
    }
  }

  /* Error recovery - if we're not in a valid finishing state, back up. */
  if (state != UTF8_ACCEPT)
    s -= 1;

  *destoff = d - dest;

  return s;
}
