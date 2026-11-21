import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

function solve(levelText: string): string {
  const rows = levelText.split('\n').filter((r) => r.length > 0);
  const w = Math.max(...rows.map((r) => r.length));
  const h = rows.length;
  const size = w * h;
  const wall = new Uint8Array(size).fill(1);
  const goal = new Uint8Array(size);
  const initialBoxes = new Set<number>();
  let playerStart = -1;

  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x];
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goal[i] = 1;
      if (ch === '$' || ch === '*') initialBoxes.add(i);
      if (ch === '@' || ch === '+') playerStart = i;
    }
  });

  const getNeighbors = (i: number, customWall?: Uint8Array) => {
    const wObj = customWall ?? wall;
    const x = i % w;
    const y = Math.floor(i / w);
    const res: number[] = [];
    if (y > 0 && !wObj[i - w]) res.push(i - w);
    if (y < h - 1 && !wObj[i + w]) res.push(i + w);
    if (x > 0 && !wObj[i - 1]) res.push(i - 1);
    if (x < w - 1 && !wObj[i + 1]) res.push(i + 1);
    return res;
  };

  const D_VECS = [-w, w, -1, 1];
  const D_NAMES = ['u', 'd', 'l', 'r'];
  const D_MAP: Record<string, number> = { u: -w, d: w, l: -1, r: 1 };

  const reachableVisited = new Uint32Array(size);
  let reachableStamp = 0;
  const reachableQ = new Int32Array(size);

  const canonVisited = new Uint32Array(size);
  let canonStamp = 0;
  const canonQ = new Int32Array(size);

  // Flood fill reachable for canonicalization
  const getCanonReachable = (start: number, validCells: Set<number>, obstacles: Set<number>) => {
    canonStamp++;
    if (!validCells.has(start) || obstacles.has(start)) return 0;
    canonQ[0] = start;
    canonVisited[start] = canonStamp;
    let head = 0;
    let tail = 1;
    while (head < tail) {
      const curr = canonQ[head++];
      const x = curr % w;
      const y = (curr / w) | 0;
      if (y > 0) {
        const next = curr - w;
        if (!wall[next] && validCells.has(next) && canonVisited[next] !== canonStamp && !obstacles.has(next)) {
          canonVisited[next] = canonStamp;
          canonQ[tail++] = next;
        }
      }
      if (y < h - 1) {
        const next = curr + w;
        if (!wall[next] && validCells.has(next) && canonVisited[next] !== canonStamp && !obstacles.has(next)) {
          canonVisited[next] = canonStamp;
          canonQ[tail++] = next;
        }
      }
      if (x > 0) {
        const next = curr - 1;
        if (!wall[next] && validCells.has(next) && canonVisited[next] !== canonStamp && !obstacles.has(next)) {
          canonVisited[next] = canonStamp;
          canonQ[tail++] = next;
        }
      }
      if (x < w - 1) {
        const next = curr + 1;
        if (!wall[next] && validCells.has(next) && canonVisited[next] !== canonStamp && !obstacles.has(next)) {
          canonVisited[next] = canonStamp;
          canonQ[tail++] = next;
        }
      }
    }
    return tail;
  };

  // Flood fill reachable
  const getReachable = (start: number, validCells: Set<number>, obstacles: Set<number>) => {
    reachableStamp++;
    if (!validCells.has(start) || obstacles.has(start)) return 0;
    reachableQ[0] = start;
    reachableVisited[start] = reachableStamp;
    let head = 0;
    let tail = 1;
    while (head < tail) {
      const curr = reachableQ[head++];
      const x = curr % w;
      const y = (curr / w) | 0;
      if (y > 0) {
        const next = curr - w;
        if (!wall[next] && validCells.has(next) && reachableVisited[next] !== reachableStamp && !obstacles.has(next)) {
          reachableVisited[next] = reachableStamp;
          reachableQ[tail++] = next;
        }
      }
      if (y < h - 1) {
        const next = curr + w;
        if (!wall[next] && validCells.has(next) && reachableVisited[next] !== reachableStamp && !obstacles.has(next)) {
          reachableVisited[next] = reachableStamp;
          reachableQ[tail++] = next;
        }
      }
      if (x > 0) {
        const next = curr - 1;
        if (!wall[next] && validCells.has(next) && reachableVisited[next] !== reachableStamp && !obstacles.has(next)) {
          reachableVisited[next] = reachableStamp;
          reachableQ[tail++] = next;
        }
      }
      if (x < w - 1) {
        const next = curr + 1;
        if (!wall[next] && validCells.has(next) && reachableVisited[next] !== reachableStamp && !obstacles.has(next)) {
          reachableVisited[next] = reachableStamp;
          reachableQ[tail++] = next;
        }
      }
    }
    return tail;
  };

  const floorCells = new Set<number>();
  for (let i = 0; i < size; i++) {
    if (!wall[i]) floorCells.add(i);
  }

  // Tarjan's articulation points
  const disc = new Int32Array(size).fill(-1);
  const low = new Int32Array(size).fill(-1);
  const isArt = new Uint8Array(size);
  let timer = 0;

  const dfsTarjan = (u: number, p: number = -1) => {
    disc[u] = low[u] = timer++;
    let children = 0;
    for (const v of getNeighbors(u)) {
      if (v === p) continue;
      if (disc[v] !== -1) {
        low[u] = Math.min(low[u], disc[v]);
      } else {
        children++;
        dfsTarjan(v, u);
        low[u] = Math.min(low[u], low[v]);
        if (p !== -1 && low[v] >= disc[u]) {
          isArt[u] = 1;
        }
      }
    }
    if (p === -1 && children > 1) {
      isArt[u] = 1;
    }
  };

  for (const f of floorCells) {
    if (disc[f] === -1) {
      dfsTarjan(f);
    }
  }

  interface Room {
    door: number;
    cells: Set<number>;
    boxes: number[];
    goals: number[];
  }

  const rawRooms: Room[] = [];

  for (let i = 0; i < size; i++) {
    if (isArt[i] && !wall[i]) {
      const door = i;
      const customWall = new Uint8Array(wall);
      customWall[door] = 1;

      const visited = new Uint8Array(size);
      for (const fc of floorCells) {
        if (fc === door || visited[fc]) continue;
        const comp = new Set<number>();
        const q = [fc];
        visited[fc] = 1;
        comp.add(fc);
        let head = 0;
        while (head < q.length) {
          const curr = q[head++];
          for (const next of getNeighbors(curr, customWall)) {
            if (!visited[next] && next !== door) {
              visited[next] = 1;
              comp.add(next);
              q.push(next);
            }
          }
        }

        let compBoxes: number[] = [];
        let compGoals: number[] = [];
        let hasPlayer = false;

        for (const c of comp) {
          if (c === playerStart) hasPlayer = true;
          if (initialBoxes.has(c)) compBoxes.push(c);
          if (goal[c]) compGoals.push(c);
        }

        if (!hasPlayer && compBoxes.length > 0 && compBoxes.length === compGoals.length) {
          const roomCells = new Set(comp);
          roomCells.add(door);
          rawRooms.push({
            door,
            cells: roomCells,
            boxes: compBoxes.sort((a, b) => a - b),
            goals: compGoals.sort((a, b) => a - b),
          });
        }
      }
    }
  }

  const byBoxKey = new Map<string, Room[]>();
  for (const r of rawRooms) {
    const key = r.boxes.join(',');
    if (!byBoxKey.has(key)) byBoxKey.set(key, []);
    byBoxKey.get(key)!.push(r);
  }

  const candidates: Room[] = [];
  for (const group of byBoxKey.values()) {
    group.sort((a, b) => a.cells.size - b.cells.size);
    candidates.push(group[0]);
  }

  let rooms: Room[] = [];
  for (const rA of candidates) {
    const setA = new Set(rA.boxes);
    const strictlyContains = candidates.some(rB => {
      if (rA === rB) return false;
      return rB.boxes.every(b => setA.has(b)) && rA.boxes.length > rB.boxes.length;
    });
    if (!strictlyContains) rooms.push(rA);
  }

  let coveredCount = 0;
  const covered = new Set<number>();
  let validPartition = true;
  for (const r of rooms) {
    for (const b of r.boxes) {
      if (covered.has(b)) validPartition = false;
      covered.add(b);
      coveredCount++;
    }
  }
  if (coveredCount !== initialBoxes.size) validPartition = false;

  if (rooms.length === 0 || !validPartition) {
    const allCells = new Set(floorCells);
    const allBoxes = Array.from(initialBoxes).sort((a, b) => a - b);
    const allGoals: number[] = [];
    for (let i = 0; i < size; i++) {
      if (goal[i]) allGoals.push(i);
    }
    rooms = [{
      door: playerStart,
      cells: allCells,
      boxes: allBoxes,
      goals: allGoals.sort((a, b) => a - b),
    }];
  }

  const solveRoom = (roomBoxes: number[], roomGoals: number[], roomCells: Set<number>, startPlayer: number, currentGlobalBoxes: Set<number>) => {
    const roomInitialBoxSet = new Set(roomBoxes);
    const otherBoxPositions = new Set([...currentGlobalBoxes].filter(b => !roomInitialBoxSet.has(b)));

    // Precompute APSP for roomCells
    const apsp = new Map<number, Map<number, number>>();
    for (const c1 of roomCells) {
      const distMap = new Map<number, number>();
      distMap.set(c1, 0);
      const q = [c1];
      let head = 0;
      while (head < q.length) {
        const curr = q[head++];
        const d = distMap.get(curr)!;
        const x = curr % w;
        const y = (curr / w) | 0;
        const neighbors = [];
        if (y > 0 && !wall[curr - w]) neighbors.push(curr - w);
        if (y < h - 1 && !wall[curr + w]) neighbors.push(curr + w);
        if (x > 0 && !wall[curr - 1]) neighbors.push(curr - 1);
        if (x < w - 1 && !wall[curr + 1]) neighbors.push(curr + 1);
        for (const next of neighbors) {
          if (roomCells.has(next) && !distMap.has(next)) {
            distMap.set(next, d + 1);
            q.push(next);
          }
        }
      }
      apsp.set(c1, distMap);
    }

    const bfsDistCached = (u: number, v: number) => {
      return apsp.get(u)?.get(v) ?? Infinity;
    };

    const deadSquares = new Set<number>();
    const boxReachableFromGoals = new Set<number>();
    const q: number[] = [];
    for (const g of roomGoals) {
      boxReachableFromGoals.add(g);
      q.push(g);
    }
    let qHead = 0;
    while (qHead < q.length) {
      const curr = q[qHead++];
      for (const d of D_VECS) {
        const prev = curr - d;
        if (roomCells.has(prev) && roomCells.has(curr - 2 * d)) {
          if (!boxReachableFromGoals.has(prev)) {
            boxReachableFromGoals.add(prev);
            q.push(prev);
          }
        }
      }
    }

    for (const c of roomCells) {
      if (!goal[c] && !boxReachableFromGoals.has(c)) {
        deadSquares.add(c);
      }
    }

    const heuristic = (boxes: number[]) => {
      if (boxes.length === 0) return 0;
      let minDist = Infinity;
      const permute = (arr: number[], m: number = arr.length) => {
        if (m === 1) {
          let dist = 0;
          for (let i = 0; i < boxes.length; i++) {
            dist += bfsDistCached(boxes[i], roomGoals[arr[i]]);
          }
          if (dist < minDist) minDist = dist;
          return;
        }
        for (let i = 0; i < m; i++) {
          permute(arr, m - 1);
          const swapIdx = m % 2 === 1 ? 0 : i;
          const tmp = arr[swapIdx];
          arr[swapIdx] = arr[m - 1];
          arr[m - 1] = tmp;
        }
      };
      const indices = roomGoals.map((_, i) => i);
      if (indices.length >= boxes.length) {
        permute(indices);
      }
      return minDist === Infinity ? 0 : minDist;
    };

    const isCornerDeadlock = (boxPos: number) => {
      if (goal[boxPos]) return false;
      const upWall = !roomCells.has(boxPos - w);
      const downWall = !roomCells.has(boxPos + w);
      const leftWall = !roomCells.has(boxPos - 1);
      const rightWall = !roomCells.has(boxPos + 1);
      return (upWall && leftWall) || (upWall && rightWall) || (downWall && leftWall) || (downWall && rightWall);
    };

    const getCanonicalState = (boxes: number[], p: number) => {
      const sortedBoxes = [...boxes].sort((a, b) => a - b);
      const allBoxSet = new Set([...otherBoxPositions, ...sortedBoxes]);
      const count = getCanonReachable(p, roomCells, allBoxSet);
      let minCell = Infinity;
      for (let i = 0; i < count; i++) {
        const c = canonQ[i];
        if (c < minCell) minCell = c;
      }
      return {
        boxKey: sortedBoxes.join(','),
        boxes: sortedBoxes,
        player: minCell === Infinity ? p : minCell,
      };
    };

    class PriorityQueue<T> {
      private heap: { item: T; priority: number }[] = [];
      push(item: T, priority: number) {
        this.heap.push({ item, priority });
        this.up(this.heap.length - 1);
      }
      pop(): T | undefined {
        if (this.heap.length === 0) return undefined;
        const top = this.heap[0].item;
        const bottom = this.heap.pop()!;
        if (this.heap.length > 0) {
          this.heap[0] = bottom;
          this.down(0);
        }
        return top;
      }
      get length() {
        return this.heap.length;
      }
      private up(i: number) {
        while (i > 0) {
          const p = Math.floor((i - 1) / 2);
          if (this.heap[i].priority < this.heap[p].priority) {
            const t = this.heap[i];
            this.heap[i] = this.heap[p];
            this.heap[p] = t;
            i = p;
          } else break;
        }
      }
      private down(i: number) {
        const len = this.heap.length;
        while (2 * i + 1 < len) {
          let left = 2 * i + 1;
          let right = left + 1;
          let smallest = i;
          if (this.heap[left].priority < this.heap[smallest].priority) smallest = left;
          if (right < len && this.heap[right].priority < this.heap[smallest].priority) smallest = right;
          if (smallest !== i) {
            const t = this.heap[i];
            this.heap[i] = this.heap[smallest];
            this.heap[smallest] = t;
            i = smallest;
          } else break;
        }
      }
    }

    interface StateNode {
      boxes: number[];
      player: number;
      g: number;
      h: number;
      pushes: { boxIdx: number; from: number; to: number; dir: string }[];
    }

    const initialState = getCanonicalState(roomBoxes, startPlayer);
    const startH = heuristic(roomBoxes);

    const pq = new PriorityQueue<StateNode>();
    pq.push(
      {
        boxes: initialState.boxes,
        player: initialState.player,
        g: 0,
        h: startH,
        pushes: [],
      },
      startH
    );

    const visitedStates = new Set<string>();
    visitedStates.add(`${initialState.boxKey}|${initialState.player}`);

    let bestSolution: { boxIdx: number; from: number; to: number; dir: string }[] | null = null;
    let expansions = 0;
    const maxExpansions = 60000;

    while (pq.length > 0 && expansions < maxExpansions) {
      expansions++;
      const curr = pq.pop()!;

      let solved = true;
      for (const b of curr.boxes) {
        if (!goal[b]) {
          solved = false;
          break;
        }
      }
      if (solved) {
        bestSolution = curr.pushes;
        break;
      }

      const allBoxSet = new Set([...otherBoxPositions, ...curr.boxes]);
      getReachable(curr.player, roomCells, allBoxSet);

      for (let bi = 0; bi < curr.boxes.length; bi++) {
        const b = curr.boxes[bi];
        for (const dName of D_NAMES) {
          const dv = D_MAP[dName];
          const behind = b - dv;
          const beyond = b + dv;

          if (reachableVisited[behind] === reachableStamp && roomCells.has(beyond) && !allBoxSet.has(beyond)) {
            if (deadSquares.has(beyond)) continue;
            if (isCornerDeadlock(beyond)) continue;

            const newBoxes = [...curr.boxes];
            newBoxes[bi] = beyond;
            const nextCanonical = getCanonicalState(newBoxes, b);

            const stateKey = `${nextCanonical.boxKey}|${nextCanonical.player}`;
            if (!visitedStates.has(stateKey)) {
              visitedStates.add(stateKey);
              const nextG = curr.g + 1;
              const nextH = heuristic(nextCanonical.boxes);
              pq.push(
                {
                  boxes: nextCanonical.boxes,
                  player: nextCanonical.player,
                  g: nextG,
                  h: nextH,
                  pushes: [...curr.pushes, { boxIdx: bi, from: b, to: beyond, dir: dName }],
                },
                nextG + nextH
              );
            }
          }
        }
      }
    }

    if (!bestSolution) return null;

    let curPlayer = startPlayer;
    let moveSeq = '';
    const workingBoxes = new Set([...otherBoxPositions, ...roomBoxes]);
    const boxMapping = new Map<number, number>();
    for (const b of roomBoxes) boxMapping.set(b, b);

    for (const p of bestSolution) {
      const dv = D_MAP[p.dir];
      const behind = p.from - dv;

      const pathMoves = findPathMoves(curPlayer, behind, workingBoxes, w, wall, roomCells);
      if (pathMoves === null) return null;
      moveSeq += pathMoves;
      moveSeq += p.dir;

      workingBoxes.delete(p.from);
      workingBoxes.add(p.to);

      for (const [initB, currB] of boxMapping.entries()) {
        if (currB === p.from) {
          boxMapping.set(initB, p.to);
          break;
        }
      }

      curPlayer = p.from;
    }

    return { moves: moveSeq, finalPlayer: curPlayer, boxMapping };
  };

  const findPathMoves = (start: number, target: number, boxes: Set<number>, w: number, wall: Uint8Array, allowedCells?: Set<number>) => {
    if (start === target) return '';
    const size = wall.length;
    const visited = new Uint8Array(size);
    const parent = new Int32Array(size).fill(-1);
    const moveDir = new Array(size);
    const q = [start];
    visited[start] = 1;
    let head = 0;

    const D_ARR = [
      { name: 'u', dv: -w },
      { name: 'd', dv: w },
      { name: 'l', dv: -1 },
      { name: 'r', dv: 1 },
    ];

    let found = false;
    while (head < q.length) {
      const curr = q[head++];
      if (curr === target) {
        found = true;
        break;
      }
      const x = curr % w;

      for (const d of D_ARR) {
        const next = curr + d.dv;
        if (next >= 0 && next < size && (!allowedCells || allowedCells.has(next)) && !wall[next] && !boxes.has(next) && !visited[next]) {
          if (d.name === 'l' && x === 0) continue;
          if (d.name === 'r' && x === w - 1) continue;
          visited[next] = 1;
          parent[next] = curr;
          moveDir[next] = d.name;
          q.push(next);
        }
      }
    }

    if (!found) return null;

    let moves = '';
    let curr = target;
    while (curr !== start) {
      moves = moveDir[curr] + moves;
      curr = parent[curr];
    }
    return moves;
  };

  let currentP = playerStart;
  let fullMoves = '';
  const currentBoxCells = new Set(initialBoxes);

  const roomBfsDist = (start: number, target: number) => {
    if (start === target) return 0;
    const visited = new Uint8Array(size);
    const q: [number, number][] = [[start, 0]];
    visited[start] = 1;
    let head = 0;
    while (head < q.length) {
      const [curr, dist] = q[head++];
      if (curr === target) return dist;
      const x = curr % w;
      const y = (curr / w) | 0;
      const neighbors = [];
      if (y > 0 && !wall[curr - w]) neighbors.push(curr - w);
      if (y < h - 1 && !wall[curr + w]) neighbors.push(curr + w);
      if (x > 0 && !wall[curr - 1]) neighbors.push(curr - 1);
      if (x < w - 1 && !wall[curr + 1]) neighbors.push(curr + 1);
      for (const next of neighbors) {
        if (!visited[next]) {
          visited[next] = 1;
          q.push([next, dist + 1]);
        }
      }
    }
    return Infinity;
  };

  rooms.sort((r1, r2) => roomBfsDist(currentP, r1.door) - roomBfsDist(currentP, r2.door));

  for (const room of rooms) {
    const path = findPathMoves(currentP, room.door, currentBoxCells, w, wall);
    if (path === null) return '';
    fullMoves += path;

    const roomRes = solveRoom(room.boxes, room.goals, room.cells, room.door, currentBoxCells);
    if (!roomRes) return '';
    fullMoves += roomRes.moves;
    currentP = roomRes.finalPlayer;

    for (const [initCell, finalCell] of roomRes.boxMapping.entries()) {
      currentBoxCells.delete(initCell);
      currentBoxCells.add(finalCell);
    }
  }

  return fullMoves;
}

for (const id of readdirSync(I).sort()) {
  const levelContent = readFileSync(join(I, id, 'level.txt'), 'utf8');
  const moves = solve(levelContent);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
