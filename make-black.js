const sharp = require('sharp');

sharp('public/logo.png')
  .modulate({ brightness: 0 })
  .toFile('public/favicon.png')
  .then(() => console.log('Done: public/favicon.png'))
  .catch(console.error);