const makeCounter = () => {
  let count = 0;
  return {
    incr: () => (count += 1),
    decr: () => (count -= 1),
  };
};
